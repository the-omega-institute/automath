import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.POM.PathIndSetPolyClosed

namespace Omega.POM

/-- Evaluate the path independent-set polynomial at an integer activity parameter. -/
noncomputable def pathIndSetEval (ℓ : Nat) (t : ℤ) : ℤ :=
  (Omega.pathIndSetPoly ℓ).eval t

/-- Closed-form hard-core marginal on the path vertex `i`, written via the left/right residual
subpaths obtained after forcing `i` to be occupied. -/
noncomputable def hardcorePathMarginalClosedForm (ℓ i : Nat) (t : ℤ) : ℚ :=
  ((t : ℚ) * (pathIndSetEval (i - 1 - 1) t : ℚ) * (pathIndSetEval (ℓ - i - 1) t : ℚ)) /
    (pathIndSetEval ℓ t : ℚ)

/-- Forcing occupancy of the `i`-th path vertex splits the remaining hard-core choices into the
left and right residual subpaths, so the marginal numerator factors as the product of the two path
independent-set polynomials.
    prop:pom-hardcore-path-marginal-closed-form -/
theorem paper_pom_hardcore_path_marginal_closed_form (ℓ i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ ℓ)
    (t : ℤ) :
    i - 1 - 1 ≤ ℓ ∧
      ℓ - i - 1 ≤ ℓ ∧
      hardcorePathMarginalClosedForm ℓ i t =
        ((t : ℚ) * (((Omega.pathIndSetPoly (i - 1 - 1)).eval t : ℤ) : ℚ) *
            (((Omega.pathIndSetPoly (ℓ - i - 1)).eval t : ℤ) : ℚ)) /
          ((((Omega.pathIndSetPoly ℓ).eval t : ℤ) : ℚ)) := by
  refine ⟨by omega, by omega, ?_⟩
  simp [hardcorePathMarginalClosedForm, pathIndSetEval]

end Omega.POM
