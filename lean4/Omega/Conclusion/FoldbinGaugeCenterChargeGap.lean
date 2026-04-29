import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-foldbin-gauge-center-charge-gap`. -/
theorem paper_conclusion_foldbin_gauge_center_charge_gap
    (s_m t_m homRank centerRank : Nat) (h_hom : homRank = s_m)
    (h_center : centerRank = t_m) (h_le : t_m ≤ s_m) :
    homRank - centerRank = s_m - t_m := by
  have _ : t_m ≤ s_m := h_le
  simp [h_hom, h_center]

end Omega.Conclusion
