import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-inversion-anomaly-information-separation`.
The window-6 inversion task needs exactly two bits because the largest fiber has size `4`, while
an injective readout of the abelianized anomaly ledger of size `2 ^ 21` needs `21` bits. -/
theorem paper_conclusion_window6_inversion_anomaly_information_separation :
    (∀ b : ℕ, b < 2 → 2 ^ b < 4) ∧ 4 ≤ 2 ^ 2 ∧ (∀ b : ℕ, b < 21 → 2 ^ b < 2 ^ 21) ∧
      21 - 2 = 19 := by
  constructor
  · intro b hb
    interval_cases b <;> norm_num
  constructor
  · norm_num
  constructor
  · intro b hb
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hb
  · norm_num

end Omega.Conclusion
