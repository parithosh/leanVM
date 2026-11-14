import Statement.LeanSphincs
import Common.Prob

/-! # The end statement is not vacuous

`Sphincs.LeanSphincsStronglyUnforgeable` bounds the adversaries within two budgets, of `π` calls
and of signing requests. These checks make sure it says something:

* `replay` spends both budgets in full: it asks for `signatureLimit = 1,182,000,000` signatures of
  message `0`, makes `k` calls of `π` itself and returns the last signature on message `1`. It
  meets both hypotheses at `q = k` (`replay_calls`, `replay_requests`).
* At `k = 2^64`, the statement bounds its winning probability by `2^-62`, far below `1`
  (`replay_bound`): the bound is not trivially true.
* A forgery on a message no request named meets the winning condition (`wins_on_unsigned_message`),
  so the game is not lost by definition.

That the verifier accepts an honest signature is checked on EthLib's vectors and leanSPHINCS's
known answer (`lean_vm`'s `scheme-vectors`, `lake exe signature-kat`). -/

open OracleComp OracleSpec Common Common.SufCma
open HashSig Sphincs Sphincs.RandomPermutationModel
open scoped ENNReal

namespace Sphincs.NonVacuity

/-- The adversary's oracles: the model's (coins, `π`, `π⁻¹`) and the signer. -/
abbrev Oracles := RandomPermutationOracles + SigningOracleSpec

/-- A signature with every field zero. -/
def zeroSignature : Signature :=
  ⟨0, fun _ ↦ ⟨0, fun _ ↦ 0⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩

/-- `n` signing requests, each of message `0`; the last answer that is a signature. -/
def requestSignatures : ℕ → OracleComp Oracles (Option Signature)
  | 0 => pure none
  | n + 1 => do
      let earlier ← requestSignatures n
      let answer : Option Signature ← liftM (Oracles.query (.inr 0))
      return answer <|> earlier

/-- `k` calls of `π`, each at the zero state. -/
def permutationCalls : ℕ → OracleComp Oracles Unit
  | 0 => pure ()
  | k + 1 => do
      let _ ← liftM (Oracles.query (.inl (.inr (.forward (Vector.replicate 25 0)))))
      permutationCalls k

-- Unfolded only by their equations: the elaborator would otherwise run `signatureLimit` requests
-- or `2^64` calls to unify a term naming them.
attribute [irreducible] requestSignatures permutationCalls

/-- **The adversary**: `signatureLimit` signatures of message `0`, `k` calls of `π`, and the last
signature offered for message `1`, which no request named. -/
def replay (k : ℕ) (_ : PublicKey) : OracleComp Oracles Forgery := do
  let last ← requestSignatures signatureLimit
  permutationCalls k
  return ⟨1, last.getD zeroSignature⟩

theorem requestSignatures_cost (w : Oracles.Domain → ℕ) (c : ℕ) (hw : ∀ r, w (.inr r) ≤ c)
    (n : ℕ) : QueryCostAtMost (requestSignatures n) w (n * c) := by
  induction n with
  | zero => rw [requestSignatures]; exact isQueryBound_pure _ _ _ _
  | succ n ih =>
    rw [requestSignatures]
    exact (ih.bind fun _ ↦ ((isWeightBound_query w _).mono (hw _)).bind
      fun _ ↦ isQueryBound_pure _ (0 : ℕ) _ _).mono (by simp [Nat.succ_mul])

theorem permutationCalls_cost (w : Oracles.Domain → ℕ) (c : ℕ) (hw : ∀ t, w (.inl t) ≤ c)
    (k : ℕ) : QueryCostAtMost (permutationCalls k) w (k * c) := by
  induction k with
  | zero => rw [permutationCalls]; exact isQueryBound_pure _ _ _ _
  | succ k ih =>
    rw [permutationCalls]
    exact (((isWeightBound_query w _).mono (hw _)).bind fun _ ↦ ih).mono
      (by rw [Nat.succ_mul, Nat.add_comm])

theorem replay_cost (w : Oracles.Domain → ℕ) (a b k : ℕ) (hreq : ∀ r, w (.inr r) ≤ a)
    (hcall : ∀ t, w (.inl t) ≤ b) (pk : PublicKey) :
    QueryCostAtMost (replay k pk) w (signatureLimit * a + (k * b + 0)) :=
  (requestSignatures_cost w a hreq _).bind fun _ ↦
    (permutationCalls_cost w b hcall k).bind fun _ ↦ isQueryBound_pure _ _ _ _

/-- `replay k` makes `k` calls of `π` itself. -/
theorem replay_calls (k : ℕ) (pk : PublicKey) :
    QueryCostAtMost (replay k pk) adversaryPermutationCost k :=
  (replay_cost adversaryPermutationCost 0 1 k (fun _ ↦ le_rfl)
    (fun t ↦ by cases t <;> simp [adversaryPermutationCost, permutationCallCost]) pk).mono
    (by simp)

/-- `replay k` makes `signatureLimit` signing requests, the most the statement allows. -/
theorem replay_requests (k : ℕ) (pk : PublicKey) :
    QueryCostAtMost (replay k pk) signingRequestCost signatureLimit :=
  (replay_cost signingRequestCost 1 0 k (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) pk).mono (by simp)

/-- **The statement, at `replay` with `2^64` calls of `π`**: it wins with probability at most
`(2^64 + 2^19) · 2^-127 ≤ 2^-62`. The hypothesis is the end statement, which
`Sphincs.leanSphincsStronglyUnforgeable` proves. -/
theorem replay_bound (h : LeanSphincsStronglyUnforgeable) :
    Pr{let b ← runWithRandomPermutation (forgeryGame sufCmaScheme (replay (2 ^ 64)))}[b = true] ≤
      2⁻¹ ^ 62 := by
  refine (h _ _ (replay_calls _) (replay_requests _)).trans ?_
  have hsum : ((2 ^ 64 : ℕ) : ℝ≥0∞) + (securitySlack : ℕ) ≤ 2 ^ 65 := by
    have : 2 ^ 64 + securitySlack ≤ 2 ^ 65 := by unfold securitySlack; norm_num
    exact_mod_cast this
  calc (((2 ^ 64 : ℕ) : ℝ≥0∞) + (securitySlack : ℕ)) * 2⁻¹ ^ 127
      ≤ 2 ^ 65 * 2⁻¹ ^ 127 := mul_le_mul_left hsum _
    _ = 2⁻¹ ^ 62 := by
      rw [show 127 = 65 + 62 from rfl, pow_add, ← mul_assoc, ← mul_pow,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- A forgery on message `1` after one request on message `0` wins. -/
theorem wins_on_unsigned_message :
    sufCmaScheme.winningCondition [⟨0, some zeroSignature⟩] ⟨1, zeroSignature⟩ = true := by
  decide

end Sphincs.NonVacuity
