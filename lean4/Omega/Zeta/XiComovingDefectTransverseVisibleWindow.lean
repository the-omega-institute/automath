import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiComovingDefectLatticeCertificateBandExclusion

namespace Omega.Zeta

private theorem sq_lt_of_abs_lt_sqrt {x A : ℝ} (hx : |x| < Real.sqrt A) : x ^ 2 < A := by
  have hA_nonneg : 0 ≤ A := by
    by_contra hAneg
    have hsqrt : Real.sqrt A = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hAneg)
    rw [hsqrt] at hx
    exact not_lt_of_ge (abs_nonneg x) hx
  have hsq : |x| ^ 2 < (Real.sqrt A) ^ 2 := by
    nlinarith [hx, abs_nonneg x, Real.sqrt_nonneg A]
  simpa [abs_sq, Real.sq_sqrt hA_nonneg] using hsq

/-- Visible-window corollary for the comoving defect certificate: membership in the explicit
window gives the expected quadratic bound, and the existing single-radius Jensen witness rules out
an off-critical zero in the same transverse band.
    thm:xi-comoving-defect-transverse-visible-window -/
theorem paper_xi_comoving_defect_transverse_visible_window
    (varrho eps delta0 x : ℝ)
    (hdelta0 : 0 < delta0 ∧ delta0 ≤ 1 / 2)
    (hx : |x| < xiComovingDefectVisibleWindow varrho eps delta0) :
    xiComovingDefectVisibleRadius varrho eps = varrho * Real.exp (-eps) ∧
      x ^ 2 <
        (((xiComovingDefectVisibleRadius varrho eps) ^ 2 * (1 + delta0) ^ 2 - (1 - delta0) ^ 2) /
          (1 - (xiComovingDefectVisibleRadius varrho eps) ^ 2)) ∧
      noOffcriticalZeroInBand 1 delta0 := by
  refine ⟨rfl, sq_lt_of_abs_lt_sqrt hx, ?_⟩
  let rho : ℝ := jensenBandRadius 1 delta0 + 1
  let Dzeta : ℝ := Real.log (rho / jensenBandRadius 1 delta0) - 1
  have hrho : jensenBandRadius 1 delta0 < rho := by
    dsimp [rho]
    linarith
  have hDzeta : Dzeta < Real.log (rho / jensenBandRadius 1 delta0) := by
    dsimp [Dzeta]
    linarith
  exact
    paper_xi_jensen_single_radius_band_exclusion 1 delta0 rho Dzeta
      (by norm_num) hdelta0 hrho hDzeta

end Omega.Zeta
