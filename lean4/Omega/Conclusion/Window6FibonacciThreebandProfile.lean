import Mathlib.Tactic

theorem paper_conclusion_window6_fibonacci_threeband_profile :
    (Finset.Icc 0 20 =
        Finset.Icc 0 8 ∪ (Finset.Icc 9 12 ∪ Finset.Icc 13 20)) ∧
      (Finset.Icc 0 8).card = 9 ∧
        (Finset.Icc 9 12).card = 4 ∧
          (Finset.Icc 13 20).card = 8 := by
  constructor
  · ext n
    simp
    omega
  · norm_num [Nat.card_Icc]
