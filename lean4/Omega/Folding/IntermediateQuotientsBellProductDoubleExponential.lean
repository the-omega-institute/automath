import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- A concrete lower-bound proxy for the number of partitions on a single fold fiber. For a
nonempty fiber we record the subset-to-partition injection used in the paper, which already yields
`2^(n-1)` choices. -/
def fiberBellChoices : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ n

@[simp] theorem fiberBellChoices_zero : fiberBellChoices 0 = 1 := rfl

@[simp] theorem fiberBellChoices_succ (n : ℕ) : fiberBellChoices (n + 1) = 2 ^ n := rfl

theorem one_le_fiberBellChoices (n : ℕ) : 1 ≤ fiberBellChoices n := by
  cases n with
  | zero =>
      simp [fiberBellChoices]
  | succ n =>
      simpa [fiberBellChoices] using (Nat.one_le_two_pow : 1 ≤ 2 ^ n)

theorem one_le_prod_fiberBellChoices (xs : List ℕ) : 1 ≤ (xs.map fiberBellChoices).prod := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simpa using one_le_mul (one_le_fiberBellChoices x) ih

/-- The chapter-local data package records the fold fibers, one distinguished largest fiber, and
the coarse exponent extracted from that fiber. -/
structure FoldIntermediateQuotientsData where
  fiberSizes : List ℕ
  maxFiber : ℕ
  growthExponent : ℕ
  maxFiber_mem : maxFiber ∈ fiberSizes
  growthExponent_le : growthExponent ≤ maxFiber - 1

namespace FoldIntermediateQuotientsData

/-- Independent partition choices on the fibers multiply. -/
def intermediateQuotientCount (D : FoldIntermediateQuotientsData) : ℕ :=
  (D.fiberSizes.map fiberBellChoices).prod

/-- The fold-intermediate quotient count factors as the product of the Bell-type fiber choices. -/
def bellProductCount (D : FoldIntermediateQuotientsData) : Prop :=
  D.intermediateQuotientCount = (D.fiberSizes.map fiberBellChoices).prod

/-- The largest fiber already contributes its Bell-type factor to the full product. -/
def maxFiberBellLowerBound (D : FoldIntermediateQuotientsData) : Prop :=
  fiberBellChoices D.maxFiber ≤ D.intermediateQuotientCount

/-- The subset-to-partition injection on the largest fiber forces a double-exponential lower bound
once the largest fiber itself grows exponentially in the fold depth. -/
def doubleExponentialGrowth (D : FoldIntermediateQuotientsData) : Prop :=
  2 ^ D.growthExponent ≤ D.intermediateQuotientCount

end FoldIntermediateQuotientsData

open FoldIntermediateQuotientsData

theorem le_prod_map_of_mem {a : ℕ} {xs : List ℕ} (ha : a ∈ xs) :
    fiberBellChoices a ≤ (xs.map fiberBellChoices).prod := by
  induction xs with
  | nil =>
      cases ha
  | cons x xs ih =>
      by_cases hax : a = x
      · subst hax
        exact Nat.le_mul_of_pos_right _ (Nat.succ_le_iff.mp (one_le_prod_fiberBellChoices xs))
      · have ha' : a ∈ xs := by simp [hax] at ha; exact ha
        have ih' := ih ha'
        have hxpos : 0 < fiberBellChoices x := Nat.succ_le_iff.mp (one_le_fiberBellChoices x)
        calc
          fiberBellChoices a ≤ (xs.map fiberBellChoices).prod := ih'
          _ ≤ fiberBellChoices x * (xs.map fiberBellChoices).prod :=
            Nat.le_mul_of_pos_left _ hxpos
          _ = ((x :: xs).map fiberBellChoices).prod := by simp

/-- Independent partition choices on each fold fiber multiply, the largest fiber contributes its
Bell-type factor, and the subset-to-partition injection on that largest fiber yields the promised
double-exponential growth witness.
    prop:fold-intermediate-quotients-bell-product-doubleexponential -/
theorem paper_fold_intermediate_quotients_bell_product_doubleexponential
    (D : FoldIntermediateQuotientsData) :
    D.bellProductCount ∧ D.maxFiberBellLowerBound ∧ D.doubleExponentialGrowth := by
  cases D with
  | mk fiberSizes maxFiber growthExponent maxFiber_mem growthExponent_le =>
      refine ⟨rfl, le_prod_map_of_mem maxFiber_mem, ?_⟩
      have hmax : fiberBellChoices maxFiber ≤ (fiberSizes.map fiberBellChoices).prod :=
        le_prod_map_of_mem maxFiber_mem
      cases maxFiber with
      | zero =>
          have hone : 1 ≤ (fiberSizes.map fiberBellChoices).prod := by
            simpa [fiberBellChoices] using hmax
          have hgrowth : growthExponent = 0 := by
            omega
          simpa [FoldIntermediateQuotientsData.doubleExponentialGrowth,
            FoldIntermediateQuotientsData.intermediateQuotientCount, fiberBellChoices, hgrowth] using hone
      | succ n =>
          have hpow : 2 ^ growthExponent ≤ 2 ^ n := by
            exact Nat.pow_le_pow_right (by omega) (by simpa using growthExponent_le)
          have hmax' : 2 ^ n ≤ (fiberSizes.map fiberBellChoices).prod := by
            simpa [fiberBellChoices] using hmax
          simpa [FoldIntermediateQuotientsData.doubleExponentialGrowth,
            FoldIntermediateQuotientsData.intermediateQuotientCount] using le_trans hpow hmax'

end Omega.Folding
