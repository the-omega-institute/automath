import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-core-determined-twisted-rh-break`. -/
theorem paper_conclusion_realinput40_core_determined_twisted_rh_break
    (rhoFull rhoCore theta : ℝ) (hfull : rhoFull = max 1 rhoCore)
    (hthreshold : (1 / 2 : ℝ) < theta -> 1 < rhoFull) :
    (1 < rhoFull -> rhoFull = rhoCore) ∧
      ((1 / 2 : ℝ) < theta -> rhoFull = rhoCore) := by
  constructor
  · intro hgt
    have hmax_gt : 1 < max 1 rhoCore := by
      simpa [hfull] using hgt
    have hnot_le : ¬ rhoCore ≤ 1 := by
      intro hle
      have hmax_eq : max 1 rhoCore = 1 := max_eq_left hle
      linarith
    have hcore_gt : 1 < rhoCore := lt_of_not_ge hnot_le
    exact hfull.trans (max_eq_right (le_of_lt hcore_gt))
  · intro htheta
    exact (show 1 < rhoFull → rhoFull = rhoCore from
      by
        intro hgt
        have hmax_gt : 1 < max 1 rhoCore := by
          simpa [hfull] using hgt
        have hnot_le : ¬ rhoCore ≤ 1 := by
          intro hle
          have hmax_eq : max 1 rhoCore = 1 := max_eq_left hle
          linarith
        have hcore_gt : 1 < rhoCore := lt_of_not_ge hnot_le
        exact hfull.trans (max_eq_right (le_of_lt hcore_gt))) (hthreshold htheta)

end Omega.Conclusion
