import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:gm-odd-schatten-spectral-norm-extremal`.
Clearing the positive denominator `((m - 1) ^ (2k))` turns the two-level odd Schatten lower
envelope into the paper polynomial inequality. -/
theorem paper_gm_odd_schatten_spectral_norm_extremal
    (m k : Nat) (hm : 2 <= m) {S1 Sodd x : Real} (_hx_left : S1 / (m : Real) <= x)
    (_hx_right : x <= S1) :
    (((m - 1 : Real) ^ (2 * k) * x ^ (2 * k + 1) + (S1 - x) ^ (2 * k + 1) <=
        (m - 1 : Real) ^ (2 * k) * Sodd) <->
      x ^ (2 * k + 1) + (m - 1 : Real) * ((S1 - x) / (m - 1 : Real)) ^ (2 * k + 1) <= Sodd) := by
  let p : Real := (m - 1 : Real) ^ (2 * k)
  let a : Real := x ^ (2 * k + 1)
  let b : Real := (S1 - x) ^ (2 * k + 1)
  have hm1_pos : 0 < (m - 1 : Real) := by
    have hm1' : 1 < (m : Real) := by
      exact_mod_cast hm
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hm1_ne : (m - 1 : Real) ≠ 0 := ne_of_gt hm1_pos
  have hrewrite :
      (m - 1 : Real) * ((S1 - x) / (m - 1 : Real)) ^ (2 * k + 1) = b / p := by
    dsimp [b, p]
    rw [div_pow]
    rw [pow_succ', div_eq_mul_inv]
    field_simp [hm1_ne]
    ring
  have hleft :
      p * (a + b / p) = p * a + b := by
    field_simp [hp_ne]
  have hright : p * Sodd = (m - 1 : Real) ^ (2 * k) * Sodd := by
    simp [p]
  have hleft' :
      p * a + b = (m - 1 : Real) ^ (2 * k) * x ^ (2 * k + 1) + (S1 - x) ^ (2 * k + 1) := by
    simp [p, a, b, mul_comm]
  have hNormalized :
      (((m - 1 : Real) ^ (2 * k) * x ^ (2 * k + 1) + (S1 - x) ^ (2 * k + 1) <=
          (m - 1 : Real) ^ (2 * k) * Sodd) ↔
        p * a + b <= p * Sodd) := by
    constructor <;> intro h <;> simpa [hleft', hright] using h
  rw [hrewrite]
  constructor
  · intro h
    have h' : p * a + b <= p * Sodd := hNormalized.mp h
    have hmul : p * (a + b / p) <= p * Sodd := by
      simpa [hleft] using h'
    nlinarith [hmul, hp_pos]
  · intro h
    have hmul : p * (a + b / p) <= p * Sodd := by
      exact mul_le_mul_of_nonneg_left h hp_pos.le
    have h' : p * a + b <= p * Sodd := by
      simpa [hleft] using hmul
    exact hNormalized.mpr h'

end Omega.SyncKernelWeighted
