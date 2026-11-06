import Lean.CoreM
import Lean.Replay

/-!
The proof gate's checks, in one process that runs no code of the project it checks
(`formal/gate/check.sh` runs it):

    lake env lean --run Gate.lean <trusted dir>... -- <root module>... -- <headline>...

1. **Which modules are checked.** The import closure of the roots, each module classified
   by where its `.olean` really is: under a trusted directory (the toolchain's library, a
   pinned dependency's build) it is a dependency, anything else is the project's. So a
   project module is checked whatever its source path (a symlink, an odd source directory,
   a file named like a lakefile): the closure, not a file listing, decides. What lies in
   a trusted directory is trusted, so the directories must hold what was fetched and
   nothing the project's build wrote: CI runs the gate in its own job for that.
2. **Kernel replay.** The dependencies are imported once, then every constant of every
   project module is replayed through the kernel over them, as `leanchecker` does. A
   declaration added without kernel checking (`debug.skipKernelTC`) is rejected here.
3. **Axioms.** Every project constant, walked through the bodies of what it uses in the
   replayed environment, depends on no axiom beyond `propext`, `Classical.choice` and
   `Quot.sound`. The walk reads only kernel-checked constants and dependencies' terms,
   never the axiom lists modules record.
4. **Statements.** On stdout, what the headlines state: one block per constant their
   types reach, through definitions' values (not theorem proofs), within the project; a
   dependency's constant by name only (its revision is pinned). Then each headline's
   axioms. `check.sh` digests the blocks and diffs them against `statements.txt`.

Dependencies are trusted, not replayed: Mathlib and the other pinned packages.
-/

open Lean

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module data of `module`, all its parts: the last one holds every constant. -/
def readModule (module : Name) : IO (Array (ModuleData × CompactedRegion)) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  readModuleDataParts fnames

/-- A constant of the kernel's environment, replayed ones included. -/
def findConst (env : Environment) (n : Name) : Option ConstantInfo :=
  env.toKernelEnv.find? n

/-- Whether `module`'s `.olean`, symlinks resolved, lies under one of `trusted`. -/
def isTrusted (trusted : Array String) (module : Name) : IO Bool := do
  let path := (← IO.FS.realPath (← findOLean module)).toString
  return trusted.any (fun dir => path.startsWith (dir ++ "/"))

/-- The axioms `n` depends on, memoized. An inductive block (its types and constructors)
is one node, so a cycle through it never leaves a partial result in the cache. -/
partial def axiomsOf (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (n : Name) : IO (Array Name) := do
  if let some a := (← cache.get)[n]? then return a
  let some ci := findConst env n | throw <| IO.userError s!"unknown constant {n}"
  let block : Array Name := match ci with
    | .inductInfo v => v.all.toArray
    | .ctorInfo v => match findConst env v.induct with
      | some (.inductInfo iv) => iv.all.toArray
      | _ => #[n]
    | _ => #[n]
  let members := block.flatMap fun i => match findConst env i with
    | some (.inductInfo iv) => #[i] ++ iv.ctors.toArray
    | _ => #[i]
  for m in members do cache.modify (·.insert m #[])
  let mut acc : Std.HashSet Name := {}
  for m in members do
    let some mi := findConst env m | throw <| IO.userError s!"unknown constant {m}"
    if mi matches .axiomInfo _ then acc := acc.insert m
    let exprs := match mi with
      | .quotInfo _ => #[]
      | .defnInfo v => #[v.type, v.value] | .thmInfo v => #[v.type, v.value]
      | .opaqueInfo v => #[v.type, v.value]
      | mi => #[mi.type]
    for e in exprs do
      for d in e.getUsedConstants do
        unless members.contains d do
          for a in ← axiomsOf env cache d do acc := acc.insert a
  let r := acc.toArray.qsort Name.lt
  for m in members do cache.modify (·.insert m r)
  return r

/-! ### Canonical statements -/

def levelText : Level → String
  | .zero => "0"
  | .succ u => s!"(succ {levelText u})"
  | .max u v => s!"(max {levelText u} {levelText v})"
  | .imax u v => s!"(imax {levelText u} {levelText v})"
  | .param n => s!"(param {n})"
  | .mvar _ => "(mvar)"

/-- An expression as one line per distinct subterm (a DAG), metadata dropped. -/
partial def exprText (e : Expr) : String := Id.run do
  let (root, (_, lines)) := (go e).run ({}, #[])
  return String.intercalate "\n" (lines.toList ++ [s!"  = #{root}"])
where
  go (e : Expr) : StateM (Std.HashMap Expr Nat × Array String) Nat := do
    if let some i := (← get).1[e]? then return i
    let node ← match e with
      | .bvar i => pure s!"bvar {i}"
      | .fvar _ => pure "fvar"
      | .mvar _ => pure "mvar"
      | .sort u => pure s!"sort {levelText u}"
      | .const n us => pure s!"const {n} [{", ".intercalate (us.map levelText)}]"
      | .app f a => return ← finish e s!"app #{← go f} #{← go a}"
      | .lam n t b bi => return ← finish e s!"lam {n} {repr bi} #{← go t} #{← go b}"
      | .forallE n t b bi => return ← finish e s!"pi {n} {repr bi} #{← go t} #{← go b}"
      | .letE n t v b nd => return ← finish e s!"let {n} {nd} #{← go t} #{← go v} #{← go b}"
      | .lit (.natVal v) => pure s!"nat {v}"
      | .lit (.strVal v) => pure s!"str {repr v}"
      | .mdata _ b => return ← go b
      | .proj s i b => return ← finish e s!"proj {s} {i} #{← go b}"
    finish e node
  finish (e : Expr) (node : String) : StateM (Std.HashMap Expr Nat × Array String) Nat :=
    modifyGet fun (seen, lines) =>
      let i := lines.size
      (i, (seen.insert e i, lines.push s!"  #{i} {node}"))

def kindText : ConstantInfo → String
  | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
  | .defnInfo d => s!"def {repr d.safety}" | .opaqueInfo d => s!"opaque unsafe={d.isUnsafe}"
  | .inductInfo i => s!"inductive params={i.numParams} indices={i.numIndices} ctors={i.ctors}"
  | .ctorInfo c => s!"ctor {c.induct} idx={c.cidx} params={c.numParams} fields={c.numFields}"
  | .recInfo _ => "recursor"

/-- The statement blocks, sorted by name. A replayed constant has no module index in the
replayed environment; a dependency's has one. -/
def statements (env : Environment) (headlines : List Name) : IO (Array String) := do
  let own (n : Name) := (env.getModuleIdxFor? n).isNone
  let mut seen : NameSet := {}
  let mut stack := headlines.toArray
  let mut blocks : Array (Name × String) := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := findConst env n | throw <| IO.userError s!"unknown constant {n}"
    if !own n then
      blocks := blocks.push (n, s!"{n}: external")
      continue
    let mut text := s!"{n}: {kindText ci} levels={ci.levelParams}\n type\n{exprText ci.type}"
    stack := stack ++ ci.type.getUsedConstants
    -- A theorem's proof is not its statement; a definition's value is.
    let value? := match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo d => some d.value
      | _ => none
    if let some v := value? then
      text := text ++ s!"\n value\n{exprText v}"
      stack := stack ++ v.getUsedConstants
    if let .inductInfo i := ci then
      stack := stack ++ i.ctors.toArray
    blocks := blocks.push (n, text)
  return (blocks.qsort (fun a b => a.1.toString < b.1.toString)).map (·.2)

unsafe def gate (trusted : Array String) (roots headlines : List Name) : IO Unit := do
  if headlines.isEmpty then throw <| IO.userError "no headline theorem named"
  -- 1. The project's modules: the import closure, up to the trusted ones.
  let mut project : Array Name := #[]
  let mut external : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut queue := roots.toArray
  let mut visited : NameSet := {}
  while h : queue.size > 0 do
    let m := queue.back
    queue := queue.pop
    if visited.contains m then continue
    visited := visited.insert m
    if ← isTrusted trusted m then
      external := external.push { module := m }
      continue
    project := project.push m
    let parts ← readModule m
    if h : parts.size = 0 then throw <| IO.userError s!"failed to read module {m}" else
    queue := queue ++ parts[0].1.imports.map (·.module)
    let last := parts[parts.size - 1].1
    for name in last.constNames, ci in last.constants do
      -- An equation lemma realized in several modules is one constant. Any repeat must be
      -- the same declaration: same kind, universe parameters, type and definition value
      -- (a theorem's proof aside, which the surviving copy's replay checks).
      if let some other := constants[name]? then
        unless kindText other == kindText ci && other.levelParams == ci.levelParams &&
            other.type == ci.type && other.value? == ci.value? do
          throw <| IO.userError s!"{name} is declared differently in two modules"
      constants := constants.insert name ci
  -- 2. The dependencies, imported once; none of them may bring a project module along.
  let (_, s) ← importModulesCore external |>.run
  let env ← finalizeImport s external {} 0 false false (isModule := true)
  for m in env.header.moduleNames do
    unless ← isTrusted trusted m do
      throw <| IO.userError s!"the dependency closure imports {m}, which is not under a trusted directory"
  let env ← env.replay constants
  IO.eprintln s!"kernel replay: {constants.size} constants of {project.size} modules"
  -- 3. Axioms, from the replayed terms.
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut bad := #[]
  -- Replay, like `leanchecker`, skips unsafe and partial constants, and the kernel rejects
  -- a safe one that uses them; every other one is in the replayed environment.
  for (name, ci) in constants do
    if ci.isUnsafe || ci.isPartial then continue
    for a in ← axiomsOf env cache name do
      unless standardAxioms.contains a do bad := bad.push s!"{name} depends on {a}"
  unless bad.isEmpty do
    throw <| IO.userError s!"axioms outside {standardAxioms}:\n{"\n".intercalate bad.toList}"
  IO.eprintln s!"axioms: {constants.size} constants within {standardAxioms}"
  -- 4. Statements, then each headline's own axioms.
  for b in ← statements env headlines do IO.println b
  for t in headlines do
    unless (constants.contains t) do
      throw <| IO.userError s!"headline {t} is not a constant of the project"
    IO.println s!"axioms of {t}: {(← axiomsOf env cache t).toList}"
  env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (trusted, rest) := args.span (· != "--")
  let (roots, rest) := (rest.drop 1).span (· != "--")
  let headlines := rest.drop 1
  let trusted ← trusted.toArray.mapM fun d => return (← IO.FS.realPath ⟨d⟩).toString
  -- In a task: the kernel recurses deeper than the main thread's stack allows on some
  -- declarations.
  match ← IO.wait (← IO.asTask (gate trusted (roots.map String.toName) (headlines.map String.toName))) with
  | .ok () => return 0
  | .error e =>
    IO.eprintln s!"proof gate failed: {e}"
    return 1
