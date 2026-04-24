import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Solving the crossing equation `Γ_q(c) = Γ_r(c)` gives the explicit branch-intersection cost.
    cor:conclusion-certificate-front-concave-polygonal-kink-support -/
theorem paper_conclusion_certificate_front_concave_polygonal_kink_support
    (Phi : Nat → ℝ) (q r : ℕ) (hq : 2 ≤ q) (hqr : q < r) :
    let cqr : ℝ := ((((q : ℝ) - 1) * Phi r - (((r : ℝ) - 1) * Phi q)) / ((r : ℝ) - (q : ℝ)))
    ((Phi q + cqr) / ((q : ℝ) - 1)) = ((Phi r + cqr) / ((r : ℝ) - 1)) := by
  dsimp
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqrR : (q : ℝ) < r := by exact_mod_cast hqr
  have hq1 : (q : ℝ) - 1 ≠ 0 := by nlinarith
  have hr1 : (r : ℝ) - 1 ≠ 0 := by nlinarith
  have hrq : (r : ℝ) - q ≠ 0 := by linarith
  field_simp [hq1, hr1, hrq]
  ring

end Omega.Conclusion
