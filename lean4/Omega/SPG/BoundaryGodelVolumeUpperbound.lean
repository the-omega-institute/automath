import Mathlib.Tactic
import Omega.SPG.AxialCoareaInequality

namespace Omega.SPG

/-- Paper-facing monotonicity wrapper: any boundary-face upper bound can be composed with the
    axial coarea estimate to obtain a bulk upper bound.
    cor:spg-dyadic-boundary-godel-volume-upperbound -/
theorem paper_spg_dyadic_boundary_godel_volume_upperbound (n L : ℕ) (N F H : ℝ) (hn : 0 < n)
    (hPrime : F ≤ H) (hCoarea : N ≤ (L : ℝ) * F / (2 * n)) :
    N ≤ (L : ℝ) * H / (2 * n) := by
  have hL : (0 : ℝ) ≤ L := by positivity
  have hDen : (0 : ℝ) ≤ 2 * n := by positivity
  have hMul : (L : ℝ) * F ≤ (L : ℝ) * H := by nlinarith
  have hDiv : (L : ℝ) * F / (2 * n) ≤ (L : ℝ) * H / (2 * n) :=
    div_le_div_of_nonneg_right hMul hDen
  exact le_trans hCoarea hDiv

end Omega.SPG
