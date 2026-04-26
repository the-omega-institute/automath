import Mathlib
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:app-jensen-finite-sampling-blindspot`. -/
theorem paper_app_jensen_finite_sampling_blindspot (a : ℂ) (radii : Finset ℝ) (ha0 : 0 < ‖a‖)
    (houtside : ∀ ρ ∈ radii, 0 < ρ ∧ ρ ≤ ‖a‖) :
    ∀ ρ ∈ radii, appSingleZeroJensenDefect ρ ({a} : Finset ℂ) = 0 := by
  intro ρ hρ
  rcases houtside ρ hρ with ⟨hρpos, hρle⟩
  unfold appSingleZeroJensenDefect
  have hdiv_nonneg : 0 ≤ ρ / ‖a‖ := by
    exact div_nonneg hρpos.le ha0.le
  have hdiv_le_one : ρ / ‖a‖ ≤ 1 := by
    exact (div_le_one ha0).2 hρle
  have hlog_nonpos : Real.log (ρ / ‖a‖) ≤ 0 := Real.log_nonpos hdiv_nonneg hdiv_le_one
  simp [max_eq_right hlog_nonpos]

end Omega.UnitCirclePhaseArithmetic
