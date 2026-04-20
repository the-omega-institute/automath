import Mathlib.Tactic

namespace Omega.GroupUnification

open scoped BigOperators

/-- The squared collision factor contributed by the transported root pair indexed by `i`. -/
def groupJGPairCollisionTerm {ι : Type*} (pairFactor : ι → ℚ) (i : ι) : ℚ :=
  pairFactor i ^ 2

/-- The collision product in the transported discriminant factorization. -/
def groupJGCollisionProduct {ι : Type*} [DecidableEq ι] (s : Finset ι) (pairFactor : ι → ℚ) :
    ℚ :=
  ∏ i ∈ s, groupJGPairCollisionTerm pairFactor i

/-- The transported discriminant after cancelling the repeated root-product powers. -/
def groupJGDiscriminantQ {ι : Type*} [DecidableEq ι] (s : Finset ι) (pairFactor : ι → ℚ)
    (leadingFactor discP rScaleFactor : ℚ) : ℚ :=
  leadingFactor * discP * rScaleFactor * groupJGCollisionProduct s pairFactor

/-- Collision criterion extracted from the factorized discriminant. -/
def groupJGHasCollision {ι : Type*} [DecidableEq ι] (s : Finset ι) (pairFactor : ι → ℚ) : Prop :=
  ∃ i ∈ s, pairFactor i = 0

/-- The transported discriminant factors into the leading term, the original discriminant, the
scale term, and the squared collision product; if the non-collision prefactors stay nonzero, then
vanishing of the transported discriminant is equivalent to the collision condition.
    thm:group-jg-discriminant-factorization -/
theorem paper_group_jg_discriminant_factorization {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (pairFactor : ι → ℚ) (leadingFactor discP rScaleFactor : ℚ)
    (hLeading : leadingFactor ≠ 0) (hDiscP : discP ≠ 0) (hScale : rScaleFactor ≠ 0) :
    groupJGDiscriminantQ s pairFactor leadingFactor discP rScaleFactor =
        leadingFactor * discP * rScaleFactor * groupJGCollisionProduct s pairFactor ∧
      (groupJGDiscriminantQ s pairFactor leadingFactor discP rScaleFactor = 0 ↔
        groupJGHasCollision s pairFactor) := by
  refine ⟨rfl, ?_⟩
  have hPrefix : leadingFactor * discP * rScaleFactor ≠ 0 :=
    mul_ne_zero (mul_ne_zero hLeading hDiscP) hScale
  constructor
  · intro hQ
    have hProdEq :
        (leadingFactor * discP * rScaleFactor) * groupJGCollisionProduct s pairFactor = 0 := by
      simpa [groupJGDiscriminantQ, mul_assoc] using hQ
    have hProd : groupJGCollisionProduct s pairFactor = 0 := by
      exact (mul_eq_zero.mp hProdEq).resolve_left hPrefix
    rw [groupJGCollisionProduct, Finset.prod_eq_zero_iff] at hProd
    rcases hProd with ⟨i, his, hi⟩
    refine ⟨i, his, ?_⟩
    exact sq_eq_zero_iff.mp <| by simpa [groupJGPairCollisionTerm] using hi
  · rintro ⟨i, his, hi⟩
    have hProd : groupJGCollisionProduct s pairFactor = 0 := by
      rw [groupJGCollisionProduct, Finset.prod_eq_zero_iff]
      exact ⟨i, his, by simp [groupJGPairCollisionTerm, hi]⟩
    simp [groupJGDiscriminantQ, hProd]

end Omega.GroupUnification
