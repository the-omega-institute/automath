import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-reversekl-gap-w2-to-delta`.
The geodesic `W₂²` proxy is controlled by the first Fourier mode, and any adjacent reverse-KL
Fourier-gap bound upgrades this to a `Δ_r` control after dividing by `a_r² r²`. -/
theorem paper_xi_reversekl_gap_w2_to_delta
    {a_r r muhat1 S_r Delta_r W2sq : ℝ}
    (ha : 0 < a_r) (hr : 0 < r) (hmu0 : 0 ≤ muhat1) (hmu1 : muhat1 ≤ 1)
    (hW2 : W2sq ≤ (Real.pi ^ 2 / 2) * (1 - muhat1))
    (hSr : r ^ 2 * (1 - muhat1 ^ 2) ≤ S_r)
    (hDelta : a_r ^ 2 * S_r ≤ Delta_r) :
    W2sq ≤ (Real.pi ^ 2 / (2 * a_r ^ 2 * r ^ 2)) * Delta_r := by
  have hmuSq : muhat1 ^ 2 ≤ muhat1 := by
    nlinarith
  have hgapMono : 1 - muhat1 ≤ 1 - muhat1 ^ 2 := by
    nlinarith
  have hW2' : W2sq ≤ (Real.pi ^ 2 / 2) * (1 - muhat1 ^ 2) := by
    nlinarith
  have hscale : a_r ^ 2 * r ^ 2 * (1 - muhat1 ^ 2) ≤ Delta_r := by
    have ha2 : 0 ≤ a_r ^ 2 := by positivity
    have haux : a_r ^ 2 * (r ^ 2 * (1 - muhat1 ^ 2)) ≤ a_r ^ 2 * S_r := by
      exact mul_le_mul_of_nonneg_left hSr ha2
    nlinarith [haux, hDelta]
  have hbase : 1 - muhat1 ^ 2 ≤ Delta_r / (a_r ^ 2 * r ^ 2) := by
    have hpos : 0 < a_r ^ 2 * r ^ 2 := by positivity
    exact (le_div_iff₀ hpos).2 <| by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hscale
  have hfinal : W2sq ≤ (Real.pi ^ 2 / 2) * (Delta_r / (a_r ^ 2 * r ^ 2)) := by
    nlinarith
  have ha0 : a_r ≠ 0 := ne_of_gt ha
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrewrite :
      (Real.pi ^ 2 / 2) * (Delta_r / (a_r ^ 2 * r ^ 2)) =
        (Real.pi ^ 2 / (2 * a_r ^ 2 * r ^ 2)) * Delta_r := by
    field_simp [ha0, hr0]
  rwa [hrewrite] at hfinal

end Omega.Zeta
