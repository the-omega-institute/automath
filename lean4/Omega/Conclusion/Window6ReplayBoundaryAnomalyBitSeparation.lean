import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-replay-boundary-anomaly-bit-separation`. -/
theorem paper_conclusion_window6_replay_boundary_anomaly_bit_separation
    (B_replay B_bdry B_anom : ℕ)
    (hreplay : B_replay = 2)
    (hbdry : B_bdry = 3)
    (hanom : B_anom = 21) :
    B_replay = 2 ∧ B_bdry = 3 ∧ B_anom = 21 ∧ B_replay < B_bdry ∧
      B_bdry < B_anom := by
  omega

end Omega.Conclusion
