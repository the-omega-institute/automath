import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ZeroTempGroundSftParryClosedForm
import Omega.Zeta.XiZeroTemperatureFourstateDeterminantStateMinimality

namespace Omega.Zeta

/-- Concrete package for the zero-temperature four-state Perron--Parry closed form.  It combines
the audited four-state determinant/minimality witness with the existing closed-form Parry data for
the corresponding four-state ground SFT. -/
structure xi_zero_temperature_fourstate_perron_parry_closed_form_data where
  groundSft :
    Omega.SyncKernelWeighted.RealInput40ZeroTempGroundSftParryClosedFormData
  fourStateMatrix : Matrix (Fin 4) (Fin 4) ℤ
  fourStateRealizes : xi_zero_temperature_fourstate_represents_hatF fourStateMatrix

namespace xi_zero_temperature_fourstate_perron_parry_closed_form_data

/-- The Perron right/left vectors, Parry transition matrix, stationary distribution, and
four-state determinant witness are all present in closed form. -/
def perron_parry_closed_form
    (D : xi_zero_temperature_fourstate_perron_parry_closed_form_data) : Prop :=
  D.groundSft.rightPerronVectorClosedForm ∧
    D.groundSft.leftPerronVectorClosedForm ∧
    D.groundSft.parryTransitionClosedForm ∧
    D.groundSft.stationaryDistributionClosedForm ∧
    xi_zero_temperature_fourstate_represents_hatF D.fourStateMatrix

end xi_zero_temperature_fourstate_perron_parry_closed_form_data

/-- Paper label: `thm:xi-zero-temperature-fourstate-perron-parry-closed-form`. The existing
four-state Parry closed-form package supplies the eigenvector, transition, and stationary-law
identities, and the determinant/minimality witness supplies the four-state realization. -/
theorem paper_xi_zero_temperature_fourstate_perron_parry_closed_form
    (D : xi_zero_temperature_fourstate_perron_parry_closed_form_data) :
    D.perron_parry_closed_form := by
  rcases
    Omega.SyncKernelWeighted.paper_killo_real_input_40_zero_temp_ground_sft_parry_closed_form
      D.groundSft with
    ⟨hRight, hLeft, hParry, hStationary⟩
  exact ⟨hRight, hLeft, hParry, hStationary, D.fourStateRealizes⟩

end Omega.Zeta
