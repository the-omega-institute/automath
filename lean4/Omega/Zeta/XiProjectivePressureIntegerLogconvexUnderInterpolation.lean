import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-projective-pressure-integer-logconvex-under-interpolation`. -/
theorem paper_xi_projective_pressure_integer_logconvex_under_interpolation
    (r τ : Nat → ℝ) (I : Set Nat)
    (hinterp : ∀ q ∈ I, Real.log (r q) = τ q)
    (hconv : ∀ q, q - 1 ∈ I → q ∈ I → q + 1 ∈ I →
      2 * τ q ≤ τ (q - 1) + τ (q + 1))
    (hpos : ∀ q ∈ I, 0 < r q) :
    (∀ q, q - 1 ∈ I → q ∈ I → q + 1 ∈ I →
      r q ^ 2 ≤ r (q - 1) * r (q + 1)) ∧
    (∀ q, q ∈ I → q + 1 ∈ I → q + 2 ∈ I →
      Real.log (r (q + 1)) - Real.log (r q) ≤
        Real.log (r (q + 2)) - Real.log (r (q + 1))) := by
  constructor
  · intro q hqm hq hqp
    have hrq : 0 < r q := hpos q hq
    have hrqm : 0 < r (q - 1) := hpos (q - 1) hqm
    have hrqp : 0 < r (q + 1) := hpos (q + 1) hqp
    have hlog :
        2 * Real.log (r q) ≤ Real.log (r (q - 1)) + Real.log (r (q + 1)) := by
      simpa [← hinterp q hq, ← hinterp (q - 1) hqm, ← hinterp (q + 1) hqp] using
        hconv q hqm hq hqp
    have hlog_le :
        Real.log (r q ^ 2) ≤ Real.log (r (q - 1) * r (q + 1)) := by
      rw [Real.log_pow, Real.log_mul hrqm.ne' hrqp.ne']
      norm_num
      exact hlog
    exact
      (Real.log_le_log_iff (pow_pos hrq 2) (mul_pos hrqm hrqp)).1 hlog_le
  · intro q hq hq1 hq2
    have hdisc :
        2 * τ (q + 1) ≤ τ q + τ (q + 2) := by
      simpa [Nat.add_assoc] using hconv (q + 1) (by simpa using hq) hq1 (by simpa using hq2)
    have hlog :
        2 * Real.log (r (q + 1)) ≤ Real.log (r q) + Real.log (r (q + 2)) := by
      simpa [← hinterp (q + 1) hq1, ← hinterp q hq, ← hinterp (q + 2) hq2] using
        hdisc
    linarith

end Omega.Zeta
