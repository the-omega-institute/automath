import Mathlib.Tactic
import Omega.Folding.OstrowskiDenominators

namespace Omega.Folding

open Omega.Folding.OstrowskiDenominators

/-- Constant-partial-quotient Ostrowski denominator sequence attached to the metallic parameter
`A`. -/
def metallicDenom (A : ℕ) : ℕ → ℕ :=
  ostrowskiDenom (fun _ => A)

/-- Left-hand weighted value in the local rule `(x, A, b) ↦ (x+1, 0, b-1)`. -/
def metallicRule1ValueLHS (A k x b : ℕ) : ℕ :=
  x * metallicDenom A (k + 2) + A * metallicDenom A (k + 1) + b * metallicDenom A k

/-- Right-hand weighted value in the local rule `(x, A, b) ↦ (x+1, 0, b-1)`. -/
def metallicRule1ValueRHS (A k x b : ℕ) : ℕ :=
  (x + 1) * metallicDenom A (k + 2) + (b - 1) * metallicDenom A k

/-- Left-hand weighted value in the local rule `(x, A+1, 0, c) ↦ (x+1, 0, A-1, c+1)`. -/
def metallicRule2ValueLHS (A k x c : ℕ) : ℕ :=
  x * metallicDenom A (k + 3) + (A + 1) * metallicDenom A (k + 2) + c * metallicDenom A k

/-- Right-hand weighted value in the local rule `(x, A+1, 0, c) ↦ (x+1, 0, A-1, c+1)`. -/
def metallicRule2ValueRHS (A k x c : ℕ) : ℕ :=
  (x + 1) * metallicDenom A (k + 3) + (A - 1) * metallicDenom A (k + 1) +
    (c + 1) * metallicDenom A k

/-- Local admissibility: every maximal digit `A` must be followed by a zero one place lower. -/
def MetallicLocalAdmissible (A : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, d (k + 1) = A → d k = 0

/-- Local irreducibility forbids both metallic trigger patterns. -/
def MetallicLocalIrreducible (A : ℕ) (d : ℕ → ℕ) : Prop :=
  ∀ k : ℕ,
    ¬ (d (k + 1) = A ∧ 0 < d k) ∧
      ¬ (d (k + 2) = A + 1 ∧ d (k + 1) = 0)

lemma metallicDenom_recurrence (A k : ℕ) :
    metallicDenom A (k + 2) = A * metallicDenom A (k + 1) + metallicDenom A k := by
  simpa [metallicDenom] using ostrowskiDenom_succ_succ (fun _ => A) k

lemma metallicDenom_recurrence_succ (A k : ℕ) :
    metallicDenom A (k + 3) = A * metallicDenom A (k + 2) + metallicDenom A (k + 1) := by
  simpa [Nat.add_assoc, metallicDenom] using ostrowskiDenom_succ_succ (fun _ => A) (k + 1)

/-- Rule 1 preserves the Ostrowski weighted value. -/
theorem metallicRule1_value_preserved (A k x b : ℕ) (hb₁ : 1 ≤ b) (_hbA : b ≤ A) :
    metallicRule1ValueLHS A k x b = metallicRule1ValueRHS A k x b := by
  rw [metallicRule1ValueLHS, metallicRule1ValueRHS, metallicDenom_recurrence]
  nth_rewrite 1 [show b = (b - 1) + 1 by omega]
  ring

/-- Rule 2 preserves the Ostrowski weighted value. -/
theorem metallicRule2_value_preserved (A k x c : ℕ) (hA : 1 ≤ A) :
    metallicRule2ValueLHS A k x c = metallicRule2ValueRHS A k x c := by
  rw [metallicRule2ValueLHS, metallicRule2ValueRHS, metallicDenom_recurrence_succ,
    metallicDenom_recurrence]
  have hA' : A = (A - 1) + 1 := by omega
  rw [hA']
  have hA'' : (A - 1) + 1 = A := by omega
  simp [hA'']
  have hsplit :
      A * metallicDenom A (k + 1) =
        metallicDenom A (k + 1) + metallicDenom A (k + 1) * (A - 1) := by
    nth_rewrite 1 [show A = 1 + (A - 1) by omega]
    ring
  rw [hsplit]
  ring

/-- Absence of the first trigger pattern implies the local admissibility constraint. -/
theorem metallicLocalIrreducible_implies_admissible {A : ℕ} {d : ℕ → ℕ}
    (h : MetallicLocalIrreducible A d) :
    MetallicLocalAdmissible A d := by
  intro k hk
  by_contra hk0
  exact (h k).1 ⟨hk, Nat.pos_of_ne_zero hk0⟩

/-- Paper label statement for the metallic two-rule normalization arithmetic package. -/
def paper_ostrowski_metallic_two_rule_normalization : Prop :=
  ∀ A : ℕ, 1 ≤ A →
    (∀ k x b : ℕ, 1 ≤ b → b ≤ A →
      metallicRule1ValueLHS A k x b = metallicRule1ValueRHS A k x b) ∧
    (∀ k x c : ℕ,
      metallicRule2ValueLHS A k x c = metallicRule2ValueRHS A k x c) ∧
    (∀ d : ℕ → ℕ, MetallicLocalIrreducible A d → MetallicLocalAdmissible A d)

/-- Proof witness for the paper-facing metallic two-rule normalization package. -/
theorem paper_ostrowski_metallic_two_rule_normalization_proof :
    paper_ostrowski_metallic_two_rule_normalization := by
  intro A hA
  refine ⟨?_, ?_, ?_⟩
  · intro k x b hb₁ hbA
    exact metallicRule1_value_preserved A k x b hb₁ hbA
  · intro k x c
    exact metallicRule2_value_preserved A k x c hA
  · intro d hd
    exact metallicLocalIrreducible_implies_admissible hd

end Omega.Folding
