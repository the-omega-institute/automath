import Mathlib.Tactic

namespace Omega.Conclusion

/-- Injectivity of the time-window encoder forces the residual ledger to carry the missing phase
volume.
    thm:conclusion-time-window-asymptotically-full-phase-law -/
theorem paper_conclusion_time_window_asymptotically_full_phase_law (T b k residualCard : Nat)
    (henc : 2 ^ (b * T) <= 2 ^ (b * k) * residualCard) : 2 ^ (b * (T - k)) <= residualCard := by
  by_cases hk : k ≤ T
  · have hsplit : b * T = b * k + b * (T - k) := by
      rw [← Nat.mul_add]
      simp [Nat.add_sub_of_le hk]
    rw [hsplit, pow_add] at henc
    exact Nat.le_of_mul_le_mul_left henc (pow_pos (by decide) _)
  · have hk' : T < k := Nat.lt_of_not_ge hk
    have hres : 1 ≤ residualCard := by
      have hpowpos : 0 < 2 ^ (b * k) := pow_pos (by decide) _
      have hrightpos : 0 < 2 ^ (b * k) * residualCard := by
        have hleftpos : 0 < 2 ^ (b * T) := pow_pos (by decide) _
        exact lt_of_lt_of_le hleftpos henc
      exact Nat.pos_of_mul_pos_left hrightpos
    simpa [Nat.sub_eq_zero_of_le (Nat.le_of_lt hk')] using hres

end Omega.Conclusion
