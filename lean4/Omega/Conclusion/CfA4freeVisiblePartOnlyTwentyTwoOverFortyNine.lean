import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete Jacobian-dimension bookkeeping for the `22/49` visible/hidden split: the three
visible quotient Jacobians have fixed dimensions `5`, `4`, `3`, the hidden Prym factor has
dimension `9`, and the ambient Jacobian has genus `49`. -/
structure conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data where
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH : ℕ
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ : ℕ
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF : ℕ
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP : ℕ
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus : ℕ
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH_eq :
    conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH = 5
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ_eq :
    conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ = 4
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF_eq :
    conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF = 3
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP_eq :
    conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP = 9
  conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus_eq :
    conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus = 49

namespace conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data

/-- The visible Jacobian block has dimension `5 + 2*4 + 3*3 = 22`. -/
def visibleDimensionTwentyTwo
    (D : conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data) : Prop :=
  D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH +
      2 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ +
      3 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF =
    22

/-- The triple Prym block has dimension `3*9 = 27`. -/
def hiddenDimensionTwentySeven
    (D : conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data) : Prop :=
  3 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP = 27

/-- The ambient genus splits as visible part plus three Prym copies, totaling `49`. -/
def jacobianDecomposition
    (D : conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data) : Prop :=
  D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus =
      (D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH +
          2 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ +
          3 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF) +
        3 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP ∧
    D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus = 49

/-- Any readout restricted to the visible block misses the hidden Prym contribution. -/
def visibleReadoutBound
    (D : conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data) : Prop :=
  D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH +
      2 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ +
      3 * D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF <
    D.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus

end conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data

/-- Paper label: `thm:conclusion-cf-a4free-visible-part-only-twenty-two-over-forty-nine`.
The visible Jacobian contribution is `22`, the hidden triple Prym contribution is `27`, the two
sum to the ambient genus `49`, and therefore any readout through the visible quotient factors
alone is strictly incomplete. -/
theorem paper_conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine
    (h : conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data) :
    h.visibleDimensionTwentyTwo /\ h.hiddenDimensionTwentySeven /\ h.jacobianDecomposition /\
      h.visibleReadoutBound := by
  have hVisible : h.visibleDimensionTwentyTwo := by
    simpa [conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data.visibleDimensionTwentyTwo,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF_eq] using
      (show (5 : ℕ) + 2 * 4 + 3 * 3 = 22 by decide)
  have hHidden : h.hiddenDimensionTwentySeven := by
    simpa [conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data.hiddenDimensionTwentySeven,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP_eq] using
      (show 3 * (9 : ℕ) = 27 by decide)
  have hDecomposition : h.jacobianDecomposition := by
    refine ⟨?_, h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus_eq⟩
    simpa [conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data.jacobianDecomposition,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimP_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus_eq] using
      (show (49 : ℕ) = (5 + 2 * 4 + 3 * 3) + 3 * 9 by decide)
  have hBound : h.visibleReadoutBound := by
    simpa [conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_data.visibleReadoutBound,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimH_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimZ_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_dimCF_eq,
      h.conclusion_cf_a4free_visible_part_only_twenty_two_over_forty_nine_totalGenus_eq] using
      (show (5 : ℕ) + 2 * 4 + 3 * 3 < 49 by decide)
  exact ⟨hVisible, hHidden, hDecomposition, hBound⟩

end Omega.Conclusion
