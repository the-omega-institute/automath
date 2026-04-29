import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-uniaxial-address-square-root-defect`. -/
theorem paper_conclusion_leyang_uniaxial_address_square_root_defect
    {F : Type*} [DecidableEq F] (n : ℕ) (axis : Finset F) (branch : Fin 5 → Finset F)
    (haxis : axis.card ≤ 2 ^ n) (hbranch : ∀ i, (branch i).card = 4 ^ n) :
    axis.card ≤ 2 ^ n ∧
      ∀ i : Fin 5, ((axis ∩ branch i).card : ℝ) / (branch i).card ≤
        1 / (2 : ℝ) ^ n := by
  refine ⟨haxis, ?_⟩
  intro i
  have hinter_card : (axis ∩ branch i).card ≤ 2 ^ n :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) haxis
  have hbranch_pos_nat : 0 < (branch i).card := by
    rw [hbranch i]
    exact pow_pos (by norm_num) n
  have hbranch_pos_real : 0 < ((branch i).card : ℝ) := by
    exact_mod_cast hbranch_pos_nat
  have hinter_card_real : ((axis ∩ branch i).card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hinter_card
  have hratio :
      ((2 ^ n : ℕ) : ℝ) / ((4 ^ n : ℕ) : ℝ) = 1 / (2 : ℝ) ^ n := by
    have htwo_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    calc
      ((2 ^ n : ℕ) : ℝ) / ((4 ^ n : ℕ) : ℝ) =
          (2 : ℝ) ^ n / (4 : ℝ) ^ n := by
        norm_num [Nat.cast_pow]
      _ = 1 / (2 : ℝ) ^ n := by
        rw [hfour]
        field_simp [htwo_ne]
  calc
    ((axis ∩ branch i).card : ℝ) / (branch i).card ≤
        ((2 ^ n : ℕ) : ℝ) / (branch i).card :=
      div_le_div_of_nonneg_right hinter_card_real (le_of_lt hbranch_pos_real)
    _ = ((2 ^ n : ℕ) : ℝ) / ((4 ^ n : ℕ) : ℝ) := by
      rw [hbranch i]
    _ = 1 / (2 : ℝ) ^ n := hratio

end Omega.Conclusion
