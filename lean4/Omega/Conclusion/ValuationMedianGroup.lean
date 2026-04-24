import Omega.Conclusion.ValuationIsometryClassification

namespace Omega.Conclusion

/-- Coordinatewise median on valuation points. -/
def conclusion_valuation_median_group_medianInt (a b c : Int) : Int :=
  max (min a b) (min (max a b) c)

/-- Coordinatewise median in the `2/3`-valuation model. -/
def conclusion_valuation_median_group_median
    (x y z : ValuationPoint) : ValuationPoint :=
  ⟨conclusion_valuation_median_group_medianInt x.v2 y.v2 z.v2,
    conclusion_valuation_median_group_medianInt x.v3 y.v3 z.v3⟩

private lemma conclusion_valuation_median_group_medianInt_between_ab (a b c : Int) :
    (a ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ b) ∨
      (b ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ a) := by
  have hbetween :
      min a b ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ max a b := by
    constructor
    · exact le_max_left _ _
    · refine max_le ?_ ?_
      · exact le_trans (min_le_left _ _) (le_max_left _ _)
      · exact min_le_left _ _
  by_cases hab : a ≤ b
  · left
    simpa [conclusion_valuation_median_group_medianInt,
      min_eq_left hab, max_eq_right hab] using hbetween
  · right
    have hba : b ≤ a := le_of_not_ge hab
    simpa [conclusion_valuation_median_group_medianInt,
      min_eq_right hba, max_eq_left hba] using hbetween

private lemma conclusion_valuation_median_group_medianInt_between_bc (a b c : Int) :
    (b ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ c) ∨
      (c ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ b) := by
  by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c
  · left
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac]
  · exfalso
    exact hac (le_trans hab hbc)
  · right
    have hcb : c ≤ b := le_of_not_ge hbc
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hcb]
  · right
    have hca : c ≤ a := le_of_not_ge hac
    have hcb : c ≤ b := le_trans hca hab
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hca, hcb]
  · left
    have hba : b ≤ a := le_of_not_ge hab
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba]
  · left
    have hba : b ≤ a := le_of_not_ge hab
    have hca : c ≤ a := le_of_not_ge hac
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba, hca]
  · exfalso
    have hba : b ≤ a := le_of_not_ge hab
    have hcb : c ≤ b := le_of_not_ge hbc
    exact hbc (le_trans hba hac)
  · right
    have hba : b ≤ a := le_of_not_ge hab
    have hcb : c ≤ b := le_of_not_ge hbc
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba, hcb]

private lemma conclusion_valuation_median_group_medianInt_between_ca (a b c : Int) :
    (c ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ a) ∨
      (a ≤ conclusion_valuation_median_group_medianInt a b c ∧
        conclusion_valuation_median_group_medianInt a b c ≤ c) := by
  by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c
  · right
    have hac' : a ≤ c := le_trans hab hbc
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hac']
  · exfalso
    exact hac (le_trans hab hbc)
  · right
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac]
  · left
    have hca : c ≤ a := le_of_not_ge hac
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hca]
  · right
    have hba : b ≤ a := le_of_not_ge hab
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba]
  · left
    have hba : b ≤ a := le_of_not_ge hab
    have hca : c ≤ a := le_of_not_ge hac
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba, hca]
  · exfalso
    have hba : b ≤ a := le_of_not_ge hab
    exact hbc (le_trans hba hac)
  · left
    have hba : b ≤ a := le_of_not_ge hab
    have hca : c ≤ a := le_of_not_ge hac
    have hcb : c ≤ b := le_of_not_ge hbc
    simp [conclusion_valuation_median_group_medianInt, hab, hbc, hac, hba, hca, hcb]

private lemma conclusion_valuation_median_group_natAbs_between
    {a b m : Int}
    (h : (a ≤ m ∧ m ≤ b) ∨ (b ≤ m ∧ m ≤ a)) :
    Int.natAbs (a - b) = Int.natAbs (a - m) + Int.natAbs (m - b) := by
  rcases h with h | h
  · rcases h with ⟨ham, hmb⟩
    rw [show a - b = (a - m) + (m - b) by ring]
    have h1 : a - m ≤ 0 := sub_nonpos_of_le ham
    have h2 : m - b ≤ 0 := sub_nonpos_of_le hmb
    simpa [h1, h2] using Int.natAbs_add_of_nonpos h1 h2
  · rcases h with ⟨hbm, hma⟩
    rw [show a - b = (a - m) + (m - b) by ring]
    have h1 : 0 ≤ a - m := sub_nonneg_of_le hma
    have h2 : 0 ≤ m - b := sub_nonneg_of_le hbm
    simpa [h1, h2] using Int.natAbs_add_of_nonneg h1 h2

private lemma conclusion_valuation_median_group_medianInt_add (t a b c : Int) :
    conclusion_valuation_median_group_medianInt (t + a) (t + b) (t + c) =
      t + conclusion_valuation_median_group_medianInt a b c := by
  simp [conclusion_valuation_median_group_medianInt, Int.min_add_left, Int.max_add_left]

private lemma conclusion_valuation_median_group_medianInt_zero_left_of_nonneg
    {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    conclusion_valuation_median_group_medianInt 0 a b = min a b := by
  have hmin : 0 ≤ min a b := le_min ha hb
  simp [conclusion_valuation_median_group_medianInt, ha, hmin]

/-- Paper-facing median-group package for the concrete `2/3`-valuation model. -/
def conclusion_valuation_median_group_statement : Prop :=
  (∀ x y z : ValuationPoint,
      let m := conclusion_valuation_median_group_median x y z
      valuationDistance x y = valuationDistance x m + valuationDistance m y ∧
        valuationDistance y z = valuationDistance y m + valuationDistance m z ∧
        valuationDistance z x = valuationDistance z m + valuationDistance m x) ∧
    (∀ a x y z : ValuationPoint,
      conclusion_valuation_median_group_median
          (valuationMul a x) (valuationMul a y) (valuationMul a z) =
        valuationMul a (conclusion_valuation_median_group_median x y z)) ∧
    (∀ x y : ValuationPoint,
      0 ≤ x.v2 → 0 ≤ y.v2 → 0 ≤ x.v3 → 0 ≤ y.v3 →
      conclusion_valuation_median_group_median valuationOne x y =
        ⟨min x.v2 y.v2, min x.v3 y.v3⟩)

abbrev ValuationMedianGroupStatement : Prop :=
  conclusion_valuation_median_group_statement

/-- Concrete median-group theorem for valuation coordinates: the coordinatewise median lies on all
three valuation geodesics, is equivariant under left multiplication, and on the nonnegative cone
the median with `1` becomes the coordinatewise minimum, i.e. the valuation avatar of `gcd`.
    thm:conclusion-valuation-median-group -/
theorem paper_conclusion_valuation_median_group : ValuationMedianGroupStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    let m := conclusion_valuation_median_group_median x y z
    have hv2xy :
        Int.natAbs (x.v2 - y.v2) =
          Int.natAbs (x.v2 - m.v2) + Int.natAbs (m.v2 - y.v2) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_ab x.v2 y.v2 z.v2)
    have hv3xy :
        Int.natAbs (x.v3 - y.v3) =
          Int.natAbs (x.v3 - m.v3) + Int.natAbs (m.v3 - y.v3) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_ab x.v3 y.v3 z.v3)
    have hv2yz :
        Int.natAbs (y.v2 - z.v2) =
          Int.natAbs (y.v2 - m.v2) + Int.natAbs (m.v2 - z.v2) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_bc x.v2 y.v2 z.v2)
    have hv3yz :
        Int.natAbs (y.v3 - z.v3) =
          Int.natAbs (y.v3 - m.v3) + Int.natAbs (m.v3 - z.v3) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_bc x.v3 y.v3 z.v3)
    have hv2zx :
        Int.natAbs (z.v2 - x.v2) =
          Int.natAbs (z.v2 - m.v2) + Int.natAbs (m.v2 - x.v2) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_ca x.v2 y.v2 z.v2)
    have hv3zx :
        Int.natAbs (z.v3 - x.v3) =
          Int.natAbs (z.v3 - m.v3) + Int.natAbs (m.v3 - x.v3) := by
      exact conclusion_valuation_median_group_natAbs_between
        (conclusion_valuation_median_group_medianInt_between_ca x.v3 y.v3 z.v3)
    refine ⟨?_, ?_, ?_⟩
    · unfold valuationDistance
      rw [hv2xy, hv3xy]
      simp [m, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · unfold valuationDistance
      rw [hv2yz, hv3yz]
      simp [m, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · unfold valuationDistance
      rw [hv2zx, hv3zx]
      simp [m, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · intro a x y z
    ext <;> simp [conclusion_valuation_median_group_median, valuationMul,
      conclusion_valuation_median_group_medianInt_add]
  · intro x y hx2 hy2 hx3 hy3
    ext <;> simp [conclusion_valuation_median_group_median, valuationOne,
      conclusion_valuation_median_group_medianInt_zero_left_of_nonneg, hx2, hy2, hx3, hy3]

end Omega.Conclusion
