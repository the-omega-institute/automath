import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound
import Omega.Zeta.XiToeplitzDiskpoleModulusClosedFormHighHeight

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The off-critical disk point obtained from the Cayley map. -/
def app_jensen_visible_threshold_offcritical_disk_zero (γ δ : ℝ) : ℂ :=
  (Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ) : ℂ)

/-- Paper label: `cor:app-jensen-visible-threshold-offcritical`. An off-critical Cayley point
inside the disk contributes the usual Jensen lower bound once the sampling radius exceeds its
modulus; the same point retains the explicit modulus formula and the high-height radial bound. -/
theorem paper_app_jensen_visible_threshold_offcritical :
    ∀ γ δ ρ : ℝ,
      0 < δ →
      0 < Omega.Zeta.appOffcriticalModSq γ δ →
      1 ≤ |γ| →
      ‖app_jensen_visible_threshold_offcritical_disk_zero γ δ‖ < ρ →
      ρ < 1 →
      Real.log (ρ / ‖app_jensen_visible_threshold_offcritical_disk_zero γ δ‖) ≤
          appSingleZeroJensenDefect ρ
            ({app_jensen_visible_threshold_offcritical_disk_zero γ δ} : Finset ℂ) ∧
        ‖app_jensen_visible_threshold_offcritical_disk_zero γ δ‖ ^ 2 =
          (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖app_jensen_visible_threshold_offcritical_disk_zero γ δ‖ ^ 2 =
          4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖app_jensen_visible_threshold_offcritical_disk_zero γ δ‖ ≤ 4 * δ / (γ ^ 2) := by
  intro γ δ ρ hδ hmodsq_pos hγ
  let w := app_jensen_visible_threshold_offcritical_disk_zero γ δ
  intro hwρ hρ1
  have hmodsq_nonneg : 0 ≤ Omega.Zeta.appOffcriticalModSq γ δ := hmodsq_pos.le
  have hnorm_eq_r :
      ‖w‖ = Omega.Zeta.xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus γ δ := by
    unfold w app_jensen_visible_threshold_offcritical_disk_zero
    unfold Omega.Zeta.xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus
    simp
  have hnorm_pos : 0 < ‖w‖ := by
    rw [hnorm_eq_r]
    exact Real.sqrt_pos.2 hmodsq_pos
  have hnorm_lt_one : ‖w‖ < 1 := by
    rw [hnorm_eq_r]
    by_contra hnot
    have hone_le : 1 ≤ Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ) := by linarith
    have : 1 ≤ Omega.Zeta.appOffcriticalModSq γ δ := by
      nlinarith [Real.sq_sqrt hmodsq_nonneg]
    linarith [Omega.Zeta.appOffcriticalModSq_lt_one γ δ hδ]
  have hsingle :=
    paper_app_jensen_single_zero_lower_bound ({w} : Finset ℂ) (a := w) (by simp) hnorm_pos
      hnorm_lt_one
  have hhigh :
      ‖w‖ ^ 2 = (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖w‖ ^ 2 = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖w‖ =
            (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + ‖w‖) ∧
        1 - ‖w‖ ≤ 4 * δ / (γ ^ 2) := by
    simpa [hnorm_eq_r] using
      Omega.Zeta.paper_xi_toeplitz_diskpole_modulus_closed_form_high_height γ δ hδ hγ
  simpa [w] using
    (show Real.log (ρ / ‖w‖) ≤ appSingleZeroJensenDefect ρ ({w} : Finset ℂ) ∧
        ‖w‖ ^ 2 = (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖w‖ ^ 2 = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
        1 - ‖w‖ ≤ 4 * δ / (γ ^ 2) from
      ⟨hsingle.1 ρ hwρ hρ1, hhigh.1, hhigh.2.1, hhigh.2.2.2⟩)

end

end Omega.UnitCirclePhaseArithmetic
