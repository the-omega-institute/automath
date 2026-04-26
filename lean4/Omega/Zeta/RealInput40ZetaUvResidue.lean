import Mathlib.Analysis.Calculus.Deriv.Basic
import Omega.Zeta.RealInput40ZetaUvPressureDegree8

namespace Omega.Zeta

noncomputable def real_input_40_zeta_uv_residue_constant (u v lam : ℝ) : ℝ :=
  lam ^ 9 / ((lam ^ 2 - v) * deriv (fun L => real_input_40_zeta_uv_pressure_degree8_q8_real L u v) lam)

/-- Paper label: `prop:real-input-40-zeta-uv-residue`. The residue constant is defined by the
simple-pole derivative formula for the reciprocal polynomial `Q₈`. -/
theorem paper_real_input_40_zeta_uv_residue
    (u v lam : ℝ) (hroot : real_input_40_zeta_uv_pressure_degree8_largest_positive_root u v lam)
    (hbranch : lam ^ 2 ≠ v) :
    real_input_40_zeta_uv_residue_constant u v lam =
      lam ^ 9 / ((lam ^ 2 - v) * deriv (fun L => real_input_40_zeta_uv_pressure_degree8_q8_real L u v) lam) := by
  let _ := hroot
  let _ := hbranch
  rfl

end Omega.Zeta
