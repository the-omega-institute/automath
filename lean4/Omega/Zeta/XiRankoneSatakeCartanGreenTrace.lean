import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-rankone-satake-cartan-green-trace`. -/
theorem paper_xi_rankone_satake_cartan_green_trace (r : ℝ) (hr : 0 < r) :
    2 * Real.log (max r r⁻¹) = 2 * max (Real.log r) (-Real.log r) ∧
      (2 * Real.log (max r r⁻¹) = 0 ↔ r = 1) := by
  have hmain : 2 * Real.log (max r r⁻¹) = 2 * max (Real.log r) (-Real.log r) := by
    by_cases hle : r ≤ r⁻¹
    · have hmax : max r r⁻¹ = r⁻¹ := max_eq_right hle
      have hlog_le : Real.log r ≤ -Real.log r := by
        have hlog_le' : Real.log r ≤ Real.log r⁻¹ :=
          Real.log_le_log hr hle
        simpa [Real.log_inv r] using hlog_le'
      have hmax_log : max (Real.log r) (-Real.log r) = -Real.log r :=
        max_eq_right hlog_le
      simp [hmax, hmax_log, Real.log_inv r]
    · have hle' : r⁻¹ ≤ r := le_of_lt (lt_of_not_ge hle)
      have hmax : max r r⁻¹ = r := max_eq_left hle'
      have hlog_le : -Real.log r ≤ Real.log r := by
        have hlog_le' : Real.log r⁻¹ ≤ Real.log r :=
          Real.log_le_log (inv_pos.mpr hr) hle'
        simpa [Real.log_inv r] using hlog_le'
      have hmax_log : max (Real.log r) (-Real.log r) = Real.log r :=
        max_eq_left hlog_le
      simp [hmax, hmax_log]
  refine ⟨hmain, ?_⟩
  constructor
  · intro hz
    have hmax_zero : max (Real.log r) (-Real.log r) = 0 := by
      have hz' : 2 * max (Real.log r) (-Real.log r) = 0 := by
        rwa [hmain] at hz
      nlinarith
    have hle_log : Real.log r ≤ 0 := by
      calc
        Real.log r ≤ max (Real.log r) (-Real.log r) := le_max_left _ _
        _ = 0 := hmax_zero
    have hle_neg_log : -Real.log r ≤ 0 := by
      calc
        -Real.log r ≤ max (Real.log r) (-Real.log r) := le_max_right _ _
        _ = 0 := hmax_zero
    have hlog_zero : Real.log r = 0 := by linarith
    have hexp : Real.exp (Real.log r) = Real.exp 0 := by rw [hlog_zero]
    simpa [Real.exp_log hr] using hexp
  · intro hr_one
    simp [hr_one]

end Omega.Zeta
