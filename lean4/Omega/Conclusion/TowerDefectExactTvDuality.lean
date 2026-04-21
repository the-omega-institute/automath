import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-fiber data for the tower-defect exact total-variation duality. The outer fiber
has cardinality `n`, while `innerCard i` records the size of the inner fiber above the `i`th outer
point. We work with the centered counts `n * (|fiber_i| + 1) - ∑_j (|fiber_j| + 1)`, which are the
uniform-versus-size-biased weights after clearing the common denominator. -/
structure TowerDefectExactTvDualityData where
  n : ℕ
  hn : 0 < n
  innerCard : Fin n → ℕ

namespace TowerDefectExactTvDualityData

/-- The common denominator coming from the size-biased normalization. -/
def totalMass (D : TowerDefectExactTvDualityData) : ℕ :=
  ∑ i : Fin D.n, (D.innerCard i + 1)

/-- The uniform-minus-size-biased defect after clearing denominators. -/
def centeredWeight (D : TowerDefectExactTvDualityData) (i : Fin D.n) : ℤ :=
  (D.n * (D.innerCard i + 1) : ℤ) - D.totalMass

/-- Signed pairing of the cleared defect against a bounded observable on one outer fiber. -/
def towerDefect (D : TowerDefectExactTvDualityData) (psi : Fin D.n → ℤ) : ℤ :=
  ∑ i : Fin D.n, D.centeredWeight i * psi i

/-- Indicator of the positive-support set of the signed defect. -/
def positiveIndicator (D : TowerDefectExactTvDualityData) (i : Fin D.n) : ℤ :=
  if 0 ≤ D.centeredWeight i then 1 else 0

/-- The total-variation norm of the cleared defect measure. -/
def totalVariation (D : TowerDefectExactTvDualityData) : ℤ :=
  ∑ i : Fin D.n, max (D.centeredWeight i) 0

/-- Vanishing of the defect means that every inner fiber has the same cardinality. -/
def constantInnerFiber (D : TowerDefectExactTvDualityData) : Prop :=
  ∃ c : ℕ, ∀ i : Fin D.n, D.innerCard i = c

/-- Paper-facing package: the positive-support indicator realizes the exact total-variation norm,
and the defect vanishes exactly for constant inner-fiber cardinalities. -/
def exactTvDuality (D : TowerDefectExactTvDualityData) : Prop :=
  D.towerDefect D.positiveIndicator = D.totalVariation ∧
    (D.totalVariation = 0 ↔ D.constantInnerFiber)

lemma totalMass_pos (D : TowerDefectExactTvDualityData) : 0 < D.totalMass := by
  let i0 : Fin D.n := ⟨0, D.hn⟩
  have hsingle : D.innerCard i0 + 1 ≤ D.totalMass := by
    unfold totalMass
    classical
    simpa using
      (Finset.single_le_sum (fun i _ => Nat.zero_le (D.innerCard i + 1)) (Finset.mem_univ i0) :
        (fun i : Fin D.n => D.innerCard i + 1) i0 ≤
          ∑ i : Fin D.n, (fun i : Fin D.n => D.innerCard i + 1) i)
  omega

lemma sum_centeredWeight (D : TowerDefectExactTvDualityData) :
    ∑ i : Fin D.n, D.centeredWeight i = 0 := by
  have hmul :
      ∑ i : Fin D.n, (D.n * (D.innerCard i + 1) : ℤ) =
        (D.n : ℤ) * D.totalMass := by
    have hmul_nat :
        ∑ i : Fin D.n, D.n * (D.innerCard i + 1) = D.n * D.totalMass := by
      unfold totalMass
      rw [← Finset.mul_sum]
    exact_mod_cast hmul_nat
  calc
    ∑ i : Fin D.n, D.centeredWeight i
        = ∑ i : Fin D.n, ((D.n * (D.innerCard i + 1) : ℤ) - D.totalMass) := by
            rfl
    _ = (∑ i : Fin D.n, (D.n * (D.innerCard i + 1) : ℤ)) -
          ∑ _i : Fin D.n, (D.totalMass : ℤ) := by
            rw [Finset.sum_sub_distrib]
    _ = (D.n : ℤ) * D.totalMass - ∑ _i : Fin D.n, (D.totalMass : ℤ) := by
            rw [hmul]
    _ = (D.n : ℤ) * D.totalMass - (D.n : ℤ) * D.totalMass := by
            simp [Finset.card_univ]
    _ = 0 := by ring

lemma centeredWeight_eq_zero_iff (D : TowerDefectExactTvDualityData) (i : Fin D.n) :
    D.centeredWeight i = 0 ↔ D.n * (D.innerCard i + 1) = D.totalMass := by
  unfold centeredWeight
  constructor
  · intro h
    have hz : (D.n * (D.innerCard i + 1) : ℤ) = D.totalMass := sub_eq_zero.mp h
    exact_mod_cast hz
  · intro h
    exact sub_eq_zero.mpr (by exact_mod_cast h)

lemma towerDefect_positiveIndicator (D : TowerDefectExactTvDualityData) :
    D.towerDefect D.positiveIndicator = D.totalVariation := by
  unfold towerDefect totalVariation positiveIndicator
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hnonneg : 0 ≤ D.centeredWeight i
  · simp [hnonneg]
  · have hlt : D.centeredWeight i < 0 := lt_of_not_ge hnonneg
    have hmax : max (D.centeredWeight i) 0 = 0 := max_eq_right (le_of_lt hlt)
    simp [hnonneg, hmax]

lemma totalVariation_eq_zero_iff_all_centered_nonpos (D : TowerDefectExactTvDualityData) :
    D.totalVariation = 0 ↔ ∀ i : Fin D.n, D.centeredWeight i ≤ 0 := by
  unfold totalVariation
  constructor
  · intro htv i
    have hsum :
        ∀ j ∈ (Finset.univ : Finset (Fin D.n)), 0 ≤ max (D.centeredWeight j) 0 := by
      intro j hj
      exact le_max_right _ _
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hsum).mp htv i (by simp)
    by_cases hnonneg : 0 ≤ D.centeredWeight i
    · have : D.centeredWeight i = 0 := by
        simpa [hnonneg] using hzero
      omega
    · exact le_of_not_ge hnonneg
  · intro hnonpos
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
    · intro i hi
      exact le_max_right _ _
    · intro i hi
      have hmax : max (D.centeredWeight i) 0 = 0 := max_eq_right (hnonpos i)
      simp [hmax]

lemma constantInnerFiber_implies_totalVariation_zero (D : TowerDefectExactTvDualityData) :
    D.constantInnerFiber → D.totalVariation = 0 := by
  rintro ⟨c, hc⟩
  unfold totalVariation
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hmass : D.totalMass = D.n * (c + 1) := by
    unfold totalMass
    simp [hc]
  have hcenter : D.centeredWeight i = 0 := by
    apply (D.centeredWeight_eq_zero_iff i).2
    simp [hc i, hmass]
  simp [hcenter]

lemma all_centered_zero_of_totalVariation_zero (D : TowerDefectExactTvDualityData)
    (htv : D.totalVariation = 0) : ∀ i : Fin D.n, D.centeredWeight i = 0 := by
  have hnonpos := (D.totalVariation_eq_zero_iff_all_centered_nonpos).mp htv
  have hneg_nonneg : ∀ i : Fin D.n, 0 ≤ -D.centeredWeight i := by
    intro i
    simpa using neg_nonneg.mpr (hnonpos i)
  have hsum_neg : ∑ i : Fin D.n, -D.centeredWeight i = 0 := by
    simpa using congrArg Neg.neg D.sum_centeredWeight
  have hzero_neg := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hneg_nonneg i)).mp hsum_neg
  intro i
  have hi := hzero_neg i (by simp)
  exact neg_eq_zero.mp hi

lemma totalVariation_zero_implies_constantInnerFiber (D : TowerDefectExactTvDualityData) :
    D.totalVariation = 0 → D.constantInnerFiber := by
  intro htv
  let i0 : Fin D.n := ⟨0, D.hn⟩
  refine ⟨D.innerCard i0, ?_⟩
  intro i
  have hi0 : D.centeredWeight i0 = 0 := D.all_centered_zero_of_totalVariation_zero htv i0
  have hi : D.centeredWeight i = 0 := D.all_centered_zero_of_totalVariation_zero htv i
  have hmass_i0 : D.n * (D.innerCard i0 + 1) = D.totalMass :=
    (D.centeredWeight_eq_zero_iff i0).mp hi0
  have hmass_i : D.n * (D.innerCard i + 1) = D.totalMass :=
    (D.centeredWeight_eq_zero_iff i).mp hi
  have hEqMul : D.n * (D.innerCard i + 1) = D.n * (D.innerCard i0 + 1) := by
    rw [hmass_i, hmass_i0]
  exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left D.hn hEqMul)

lemma totalVariation_zero_iff_constantInnerFiber (D : TowerDefectExactTvDualityData) :
    D.totalVariation = 0 ↔ D.constantInnerFiber := by
  constructor
  · exact D.totalVariation_zero_implies_constantInnerFiber
  · exact D.constantInnerFiber_implies_totalVariation_zero

end TowerDefectExactTvDualityData

open TowerDefectExactTvDualityData

/-- Paper label: `thm:conclusion-pom-tower-defect-exact-tv-duality`. On one outer fiber, the
cleared tower defect is exactly paired with the indicator of its positive support, and it vanishes
exactly when the uniform and size-biased fiber weights coincide, equivalently when the inner fiber
cardinality is constant. -/
theorem paper_conclusion_pom_tower_defect_exact_tv_duality
    (D : TowerDefectExactTvDualityData) : D.exactTvDuality := by
  exact ⟨D.towerDefect_positiveIndicator, D.totalVariation_zero_iff_constantInnerFiber⟩

end Omega.Conclusion
