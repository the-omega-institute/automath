import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The affine determinant polynomial of the `2 × 2` Hankel seed
`[[a₀, a₁], [a₁, x]]`. -/
def hankelSeedDet {p : ℕ} [Fact p.Prime] (a0 a1 x : ZMod p) : ZMod p :=
  a0 * x - a1 ^ (2 : ℕ)

/-- The one-step completion equation solved by the nondegenerate leading coefficient `a₀`. -/
def hankelSeedCompletionEq {p : ℕ} [Fact p.Prime] (a0 a1 x y : ZMod p) : Prop :=
  a0 * y = a1 * x

/-- Finite-field failure set for the determinant-vanishing locus. -/
def hankelSeedFailureSet {p : ℕ} [Fact p.Prime] (a0 a1 : ZMod p) : Type :=
  {x : ZMod p // hankelSeedDet a0 a1 x = 0}

/-- The determinant-vanishing locus has cardinality at most one, hence probability at most `1/p`
under a uniform sample from `ZMod p`. -/
def hankelSeedFailureProbabilityBound {p : ℕ} [Fact p.Prime] (a0 a1 : ZMod p) : Prop :=
  Subsingleton (hankelSeedFailureSet a0 a1)

/-- On the nonvanishing locus, the next step of the affine Hankel completion is unique. -/
def hankelSeedUniqueExtensionOnNonvanishingLocus {p : ℕ} [Fact p.Prime]
    (a0 a1 : ZMod p) : Prop :=
  ∀ x : ZMod p, hankelSeedDet a0 a1 x ≠ 0 → ∃! y : ZMod p, hankelSeedCompletionEq a0 a1 x y

/-- Finite-field seed for random Hankel completion in the nondegenerate case:
the determinant polynomial of the affine `2 × 2` Hankel family has at most one zero, and away
from that vanishing locus the next-step completion is unique.
    thm:xi-hankel-finitefield-random-completion-nondegenerate -/
theorem paper_xi_hankel_finitefield_random_completion_nondegenerate
    {p : ℕ} [Fact p.Prime] (a0 a1 : ZMod p) (ha0 : a0 ≠ 0) :
    hankelSeedFailureProbabilityBound a0 a1 ∧
      hankelSeedUniqueExtensionOnNonvanishingLocus a0 a1 := by
  haveI : Subsingleton (hankelSeedFailureSet a0 a1) := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    have hx : a0 * x.1 = a1 ^ (2 : ℕ) := by
      exact sub_eq_zero.mp (by simpa [hankelSeedDet] using x.2)
    have hy : a0 * y.1 = a1 ^ (2 : ℕ) := by
      exact sub_eq_zero.mp (by simpa [hankelSeedDet] using y.2)
    apply mul_left_cancel₀ ha0
    rw [hx, hy]
  refine ⟨?_, ?_⟩
  · unfold hankelSeedFailureProbabilityBound
    infer_instance
  · intro x hx
    refine ⟨a0⁻¹ * a1 * x, ?_, ?_⟩
    · unfold hankelSeedCompletionEq
      calc
        a0 * (a0⁻¹ * a1 * x) = (a0 * a0⁻¹) * (a1 * x) := by ac_rfl
        _ = a1 * x := by simp [ha0]
    · intro y hy
      apply mul_left_cancel₀ ha0
      calc
        a0 * y = a1 * x := hy
        _ = a0 * (a0⁻¹ * a1 * x) := by
          calc
            a1 * x = (a0 * a0⁻¹) * (a1 * x) := by simp [ha0]
            _ = a0 * (a0⁻¹ * a1 * x) := by ac_rfl

end Omega.Zeta
