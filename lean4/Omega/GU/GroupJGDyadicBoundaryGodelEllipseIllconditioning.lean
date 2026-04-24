import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.GU.GodelConditionNumberIdentity

namespace Omega.GU

/-- The Lorentz-block condition number attached to a dyadic boundary Gödel code `H`. -/
noncomputable def dyadicBoundaryEllipseConditionNumber (H : ℕ) : ℝ :=
  godelLorentzConditionNumber (H : ℝ)

/-- A concrete lower envelope for the boundary Gödel code coming from a dyadic `(n-1)`-dimensional
boundary scale. -/
def dyadicBoundaryGodelLowerBound (n N : ℕ) : ℕ :=
  N ^ (n - 1)

/-- Paper label: `cor:group-jg-dyadic-boundary-godel-ellipse-illconditioning`. Instantiating the
verified condition-number identity at a boundary Gödel code `H` turns any concrete lower bound on
`H` into a logarithmic lower bound for the corresponding ellipse condition number. -/
theorem paper_group_jg_dyadic_boundary_godel_ellipse_illconditioning
    (n N H : ℕ) (hN : 0 < N) (hH : 1 < H)
    (hLower : dyadicBoundaryGodelLowerBound n N ≤ H) :
    dyadicBoundaryEllipseConditionNumber H = H ∧
      Real.log (dyadicBoundaryEllipseConditionNumber H) ≥
        Real.log (dyadicBoundaryGodelLowerBound n N) := by
  have hcond :
      godelLorentzConditionNumber (H : ℝ) = (H : ℝ) := by
    simpa using
      (paper_group_jg_godel_condition_number_identity (H : ℝ) (by exact_mod_cast hH)).2.2
  have hLowerReal : (dyadicBoundaryGodelLowerBound n N : ℝ) ≤ H := by
    exact_mod_cast hLower
  have hLowerPos : 0 < (dyadicBoundaryGodelLowerBound n N : ℝ) := by
    exact_mod_cast pow_pos hN (n - 1)
  have hHReal : 0 < (H : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hH)
  refine ⟨?_, ?_⟩
  · simpa [dyadicBoundaryEllipseConditionNumber] using hcond
  · rw [dyadicBoundaryEllipseConditionNumber, hcond]
    exact Real.log_le_log hLowerPos hLowerReal

end Omega.GU
