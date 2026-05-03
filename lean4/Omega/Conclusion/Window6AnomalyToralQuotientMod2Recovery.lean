import Mathlib.Tactic

/-- Paper-label helper for the mod-two root channels. -/
def conclusion_window6_anomaly_toral_quotient_mod2_recovery_rootChannels : ℕ := 18

/-- Paper-label helper for the toral two-torsion channels. -/
def conclusion_window6_anomaly_toral_quotient_mod2_recovery_toralChannels : ℕ := 3

/-- Paper-label helper for the recovered anomaly parity dimension. -/
def conclusion_window6_anomaly_toral_quotient_mod2_recovery_totalChannels : ℕ := 21

/-- Paper label: `cor:conclusion-window6-anomaly-toral-quotient-mod2-recovery`. -/
theorem paper_conclusion_window6_anomaly_toral_quotient_mod2_recovery :
    18 + 3 = 21 ∧ (2 : ℕ) ^ 18 * 2 ^ 3 = 2 ^ 21 := by
  norm_num [pow_succ, pow_add]
