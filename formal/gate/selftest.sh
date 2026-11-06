#!/usr/bin/env bash
# The proof gate tested end to end: compiled mutations in a throwaway project, each of
# which `check.sh` must reject for the right reason, and the unmutated project it must
# pass. Core Lean only, no Mathlib.
#
#   formal/gate/selftest.sh <lean-toolchain file>
set -euo pipefail

gate="${GATE_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
toolchain="$(realpath "$1")"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
p="$work/gst"

clean='import Lean

def f : Nat := 1

def pair.{u, v} (α : Sort u) (β : Sort v) : Sort (max 1 u v) := PProd α β

private def secret : Nat := 3

def g : Nat := secret

theorem headline : f = 1 ∧ Nonempty (pair Nat Bool) ∧ g = g := ⟨rfl, ⟨⟨0, true⟩⟩, rfl⟩'

# A declaration of `False` the kernel never checked, with no banned word in the source:
# `lake build`, `#print axioms` and a text search all pass it.
bypass='open Lean Elab Command in
run_cmd liftCoreM do
  let decl := Declaration.thmDecl
    { name := `bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  withOptions (fun o => o.setBool (Name.mkStr2 "debug" "skipKernelTC") true) (addDecl decl)'
evil="import Lean

$bypass"

# project <Gst.lean source> [lakefile additions]: a fresh project, built.
project() {
  rm -rf "$p"
  mkdir -p "$p"
  cp "$toolchain" "$p/lean-toolchain"
  printf 'name = "gst"\ndefaultTargets = ["Gst"]\n%s\n\n[[lean_lib]]\nname = "Gst"\n' "${2:-}" >"$p/lakefile.toml"
  printf '%s\n' "$1" >"$p/Gst.lean"
}
build() { (cd "$p" && lake build -q); }

# expect_fail <name> <text the failure must contain>, against the pinned statements.
expect_fail() {
  cp "$work/statements.txt" "$p/statements.txt"
  if "$gate/check.sh" "$p" headline >"$work/$1.log" 2>&1; then
    echo "FAIL: the gate passed the $1 mutation" >&2
    exit 1
  fi
  if ! grep -qF -- "$2" "$work/$1.log"; then
    echo "FAIL: the gate rejected the $1 mutation, but not with \"$2\":" >&2
    cat "$work/$1.log" >&2
    exit 1
  fi
  echo "ok: $1 rejected"
}

project "$clean"
build
"$gate/check.sh" --update "$p" headline >"$work/update.log" 2>&1 || {
  cat "$work/update.log" >&2
  echo "FAIL: the gate could not pin the unmutated project" >&2
  exit 1
}
cp "$p/statements.txt" "$work/statements.txt"
"$gate/check.sh" "$p" headline >"$work/clean.log" 2>&1 || {
  cat "$work/clean.log" >&2
  echo "FAIL: the gate rejected the unmutated project" >&2
  exit 1
}
echo "ok: unmutated project passes"

project "$clean

$bypass

theorem unsound : (1 : Nat) = 2 := bogus.elim"
build
expect_fail kernel-bypass "declaration type mismatch, 'bogus'"

# The same bypass in a module that no file listing names: behind a symlinked directory,
# in a file named like a lakefile, and in a library whose sources sit under .lake.
mkdir -p "$work/outside/Sub"
printf '%s\n' "$evil" >"$work/outside/Sub/Evil.lean"
project "import Gst.Sub.Evil
$clean"
mkdir -p "$p/Gst" && ln -s "$work/outside/Sub" "$p/Gst/Sub"
build
expect_fail symlinked-module "declaration type mismatch, 'bogus'"

project "import Gst.lakefile
$clean"
mkdir -p "$p/Gst"
printf '%s\n' "$evil" >"$p/Gst/lakefile.lean"
build
expect_fail lakefile-named-module "declaration type mismatch, 'bogus'"

project "import Evil
$clean" '
[[lean_lib]]
name = "Evil"
srcDir = ".lake/hidden"'
mkdir -p "$p/.lake/hidden"
printf '%s\n' "$evil" >"$p/.lake/hidden/Evil.lean"
build
expect_fail hidden-source-module "declaration type mismatch, 'bogus'"

# An axiom declared without the `axiom` keyword, which the kernel accepts.
project "$clean

open Lean Elab Command in
run_cmd liftCoreM do
  addDecl (.axiomDecl { name := \`ax, levelParams := [], type := mkConst \`\`False, isUnsafe := false })

theorem unsound : (1 : Nat) = 2 := ax.elim"
build
expect_fail custom-axiom "unsound depends on ax"

# Project code that would report success if it ran inside the gate, which it must not.
project "$clean

initialize do
  IO.println \"proof gate passed\"
  IO.Process.exit 0

open Lean Elab Command in
run_cmd liftCoreM do
  addDecl (.axiomDecl { name := \`ax, levelParams := [], type := mkConst \`\`False, isUnsafe := false })

theorem unsound : (1 : Nat) = 2 := ax.elim"
build
expect_fail project-initializer "unsound depends on ax"

project "$clean

theorem unfinished : (1 : Nat) = 2 := sorry"
build
expect_fail sorry "unfinished depends on sorryAx"

# What the headline states, changed: a definition it uses, universe parameters in the
# other order, a private definition under an unchanged public one, and its axioms.
changed="${clean/def f : Nat := 1/def f : Nat := 2}"
project "${changed/f = 1/f = 2}"
build
expect_fail definition-change "-f "

project "${clean/pair.\{u, v\}/pair.\{v, u\}}"
build
expect_fail universe-order "-pair "

project "${clean/secret : Nat := 3/secret : Nat := 4}"
build
expect_fail private-definition "-_private"

project "${clean/rfl, ⟨⟨0, true⟩⟩, rfl⟩/(Classical.em True).elim (fun _ => rfl) (fun _ => rfl), ⟨⟨0, true⟩⟩, rfl⟩}"
build
expect_fail headline-axioms "-axioms of headline: []"

# A definition the headline uses, changed in a module behind a symlinked directory.
mkdir -p "$work/outside2/Sub"
printf 'def Secure (n : Nat) : Prop := n ≥ 128\n' >"$work/outside2/Sub/Def.lean"
project "import Gst.Sub.Def

theorem headline : Secure 200 := by unfold Secure; decide"
mkdir -p "$p/Gst" && ln -s "$work/outside2/Sub" "$p/Gst/Sub"
build
"$gate/check.sh" --update "$p" headline >"$work/update2.log" 2>&1 || { cat "$work/update2.log" >&2; exit 1; }
cp "$p/statements.txt" "$work/statements.txt"
printf 'def Secure (n : Nat) : Prop := n ≥ 1\n' >"$work/outside2/Sub/Def.lean"
build
expect_fail symlinked-definition "-Secure "

# A dependency that is a path, not a pinned revision.
mkdir -p "$work/helper"
cp "$toolchain" "$work/helper/lean-toolchain"
printf 'name = "helper"\n\n[[lean_lib]]\nname = "Helper"\n' >"$work/helper/lakefile.toml"
printf 'def h : Nat := 1\n' >"$work/helper/Helper.lean"
project "import Helper
$clean" '
[[require]]
name = "helper"
path = "../helper"'
build
expect_fail path-dependency "dependency helper is a path package"

# A toolchain from another origin.
project "$clean"
build
echo "someone/lean4:v4.31.0" >"$p/lean-toolchain"
expect_fail toolchain-origin "must name a leanprover/lean4 release"

# A lakefile that runs code, and a symlink in the build directory.
project "$clean"
build
printf 'import Lake\nopen Lake DSL\npackage gst\n' >"$p/lakefile.lean"
expect_fail lakefile-lean "lakefile.lean runs code"

project "$clean"
build
ln -s /tmp "$p/.lake/build/lib/lean/Elsewhere"
expect_fail build-symlink "the build directory holds symlinks"

project "$clean"
build
mkfifo "$p/.lake/build/lib/lean/Gst/Pipe.olean" 2>/dev/null || { mkdir -p "$p/.lake/build/lib/lean/Gst" && mkfifo "$p/.lake/build/lib/lean/Gst/Pipe.olean"; }
expect_fail build-fifo "neither files nor directories"

echo "== gate self-test passed"
