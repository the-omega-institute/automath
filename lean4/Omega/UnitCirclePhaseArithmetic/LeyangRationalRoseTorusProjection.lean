import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.UnitaryDeterminantZeroUnitCircle

namespace Omega.UnitCirclePhaseArithmetic

/-- The torus projection `w = (η/2)(ξ + ξ⁻¹)` preserves the radial trace coordinate up to the
unit-circle phase `η`, so the singular-ring inverse-square coordinate depends only on
`|ξ + ξ⁻¹|`. -/
theorem paper_leyang_rational_rose_torus_projection (xi eta : ℂ) (hxi : Complex.abs xi = 1)
    (heta : Complex.abs eta = 1) (hw0 : ((eta / 2) * (xi + xi⁻¹)) ≠ 0) :
    let w : ℂ := (eta / 2) * (xi + xi⁻¹)
    Complex.abs w = Complex.abs (xi + xi⁻¹) / 2 ∧
      -(1 / (4 * Complex.abs w ^ 2 : ℝ)) = -(1 / (Complex.abs (xi + xi⁻¹) ^ 2 : ℝ)) := by
  let _ := hxi
  dsimp
  have hsum0 : xi + xi⁻¹ ≠ 0 := by
    intro hsum
    apply hw0
    simp [hsum]
  have hsum_abs0 : Complex.abs (xi + xi⁻¹) ≠ 0 := by
    simp [Complex.abs, hsum0]
  have heta_div :
      Complex.abs (eta / 2) = 1 / 2 := by
    calc
      Complex.abs (eta / 2) = Complex.abs eta / Complex.abs (2 : ℂ) := by
        simp [Complex.abs]
      _ = 1 / 2 := by
        rw [heta]
        norm_num [Complex.abs]
  have h_abs :
      Complex.abs ((eta / 2) * (xi + xi⁻¹)) = Complex.abs (xi + xi⁻¹) / 2 := by
    calc
      Complex.abs ((eta / 2) * (xi + xi⁻¹)) = Complex.abs (eta / 2) * Complex.abs (xi + xi⁻¹) := by
        simp [Complex.abs]
      _ = (1 / 2) * Complex.abs (xi + xi⁻¹) := by rw [heta_div]
      _ = Complex.abs (xi + xi⁻¹) / 2 := by ring_nf
  refine ⟨h_abs, ?_⟩
  rw [h_abs]
  field_simp [hsum_abs0]
  ring_nf

end Omega.UnitCirclePhaseArithmetic
