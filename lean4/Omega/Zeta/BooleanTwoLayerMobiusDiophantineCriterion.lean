import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerInverseSupportLaw

namespace Omega.Zeta

/-- The Boolean two-layer diagonal coefficient after conjugating by the existing Boolean `ζ/μ`
package: the empty subset carries the top coefficient `a`, while every nonempty subset carries the
lower-layer coefficient `a - b`. -/
def booleanTwoLayerDiagonalCoefficient {q : ℕ} (a b : ℤ) (U : BooleanSubset q) : ℤ :=
  if U = ∅ then a else a - b

/-- Coordinatewise divisibility condition for the diagonalized Boolean two-layer integer system. -/
def booleanTwoLayerCoordinateDivisibility {q : ℕ} (a b : ℤ) (y : BooleanSubset q → ℤ) : Prop :=
  a ∣ y ∅ ∧ ∀ U : BooleanSubset q, U ≠ ∅ → a - b ∣ y U

/-- The diagonalized Boolean two-layer system obtained from the existing `ζ/μ` package. -/
def booleanTwoLayerDiagonalSystem {q : ℕ} (a b : ℤ) (y z : BooleanSubset q → ℤ) : Prop :=
  ∀ U : BooleanSubset q, y U = booleanTwoLayerDiagonalCoefficient a b U * z U

/-- Paper-facing Möbius/Diophantine criterion for the Boolean two-layer system: after the
`ζ/μ` conjugation, solvability over `ℤ` is exactly the coordinatewise divisibility condition on the
diagonal coordinates. The already formalized inverse-support package records the underlying Boolean
two-layer conjugation data.
    thm:xi-boolean-two-layer-mobius-diophantine-criterion -/
def BooleanTwoLayerMobiusDiophantineCriterion (q : ℕ) (a b : ℤ)
    (y : BooleanSubset q → ℤ) : Prop :=
  BooleanTwoLayerInverseSupportLaw q a b ∧
    (booleanTwoLayerCoordinateDivisibility a b y ↔
      ∃ z : BooleanSubset q → ℤ, booleanTwoLayerDiagonalSystem a b y z)

theorem paper_xi_boolean_two_layer_mobius_diophantine_criterion (q : ℕ) (hq : 2 ≤ q) (a b : ℤ)
    (y : Omega.Zeta.BooleanSubset q → ℤ) : BooleanTwoLayerMobiusDiophantineCriterion q a b y := by
  refine ⟨paper_xi_boolean_two_layer_inverse_support_law q hq a b, ?_⟩
  constructor
  · rintro ⟨hEmpty, hNonempty⟩
    rcases hEmpty with ⟨z0, hz0⟩
    refine ⟨fun U => if hU : U = ∅ then z0 else Classical.choose (hNonempty U hU), ?_⟩
    intro U
    by_cases hU : U = ∅
    · subst hU
      simp [booleanTwoLayerDiagonalCoefficient, hz0]
    · have hzU : y U = (a - b) * Classical.choose (hNonempty U hU) :=
        Classical.choose_spec (hNonempty U hU)
      rw [show booleanTwoLayerDiagonalCoefficient a b U = a - b by
        simp [booleanTwoLayerDiagonalCoefficient, hU]]
      simpa [hU] using hzU
  · rintro ⟨z, hz⟩
    refine ⟨?_, ?_⟩
    · refine ⟨z ∅, ?_⟩
      simpa [booleanTwoLayerDiagonalCoefficient] using hz ∅
    · intro U hU
      refine ⟨z U, ?_⟩
      simpa [booleanTwoLayerDiagonalCoefficient, hU] using hz U

end Omega.Zeta
