import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.JensenCountableCriterion

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion
open JensenCountableCriterionData

/-- RH is equivalent to vanishing Jensen defect on every radius layer in the finiteization
interface.
    cor:app-rh-iff-jensen-defect-zero -/
theorem paper_app_rh_iff_jensen_defect_zero (D : JensenCountableCriterionData) :
    D.rh ↔ ∀ {rho : ℝ}, 0 < rho → rho < 1 → D.defect rho = 0 := by
  constructor
  · intro hRh rho hrho hrho_lt
    exact (D.semantics rho hrho hrho_lt).2.mpr (hRh hrho hrho_lt)
  · intro hDefect rho hrho hrho_lt
    exact (D.semantics rho hrho hrho_lt).2.mp (hDefect hrho hrho_lt)

end Omega.UnitCirclePhaseArithmetic
