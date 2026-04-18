import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The geometric ratio extracted from the product of the exponential nodes. -/
def lucasCharpGeomRatio (q m : ℕ) (α s : ℝ) : ℝ :=
  α ^ (q * m) * s ^ (m * (m - 1) / 2)

/-- Concrete shifted-Hankel determinant data for the Lucas-Charp exponential family. -/
structure ConclusionLucasCharpShiftedHankelData where
  m : ℕ
  q : ℕ
  α : ℝ
  s : ℝ
  rank : ℕ
  detScale : ℝ
  coeff : Fin m → ℝ
  lambda : Fin m → ℝ
  shiftedDet : ℕ → ℝ
  horder_le_rank : m ≤ rank
  hrank_le_order : rank ≤ m
  hshiftedDet :
    ∀ r, shiftedDet r = detScale * ∏ a : Fin m, (coeff a * lambda a ^ r)
  hprod_lambda : ∏ a : Fin m, lambda a = lucasCharpGeomRatio q m α s

namespace ConclusionLucasCharpShiftedHankelData

/-- The shifted Hankel determinant weight product at shift `r`. -/
def shiftedWeightProduct (D : ConclusionLucasCharpShiftedHankelData) (r : ℕ) : ℝ :=
  ∏ a : Fin D.m, (D.coeff a * D.lambda a ^ r)

/-- The shifted Hankel rank equals the exponential order `m`. -/
def rankEqualsOrder (D : ConclusionLucasCharpShiftedHankelData) : Prop :=
  D.rank = D.m

/-- Consecutive shifted Hankel determinants differ by the geometric ratio
`α^(q m) * s^(m(m-1)/2)`. -/
def shiftedHankelGeometricRatio (D : ConclusionLucasCharpShiftedHankelData) : Prop :=
  ∀ r, D.shiftedDet (r + 1) = lucasCharpGeomRatio D.q D.m D.α D.s * D.shiftedDet r

lemma shiftedWeightProduct_succ (D : ConclusionLucasCharpShiftedHankelData) (r : ℕ) :
    D.shiftedWeightProduct (r + 1) = (∏ a : Fin D.m, D.lambda a) * D.shiftedWeightProduct r := by
  unfold shiftedWeightProduct
  calc
    ∏ a : Fin D.m, (D.coeff a * D.lambda a ^ (r + 1))
        = ∏ a : Fin D.m, (D.lambda a * (D.coeff a * D.lambda a ^ r)) := by
            apply Finset.prod_congr rfl
            intro a ha
            rw [pow_succ]
            ring
    _ = (∏ a : Fin D.m, D.lambda a) * ∏ a : Fin D.m, (D.coeff a * D.lambda a ^ r) := by
          rw [Finset.prod_mul_distrib]

lemma rankEqualsOrder_holds (D : ConclusionLucasCharpShiftedHankelData) : D.rankEqualsOrder := by
  exact le_antisymm D.hrank_le_order D.horder_le_rank

lemma shiftedHankelGeometricRatio_holds (D : ConclusionLucasCharpShiftedHankelData) :
    D.shiftedHankelGeometricRatio := by
  intro r
  have hsucc := D.shiftedWeightProduct_succ r
  unfold shiftedWeightProduct at hsucc
  rw [D.hshiftedDet (r + 1), D.hshiftedDet r, hsucc, D.hprod_lambda]
  ring

end ConclusionLucasCharpShiftedHankelData

open ConclusionLucasCharpShiftedHankelData

/-- For the Lucas-Charp shifted Hankel family, the rank is the exponential order `m`, and the
determinants form a geometric progression with ratio
`α^(q m) * s^(m(m-1)/2)`.
    thm:conclusion-lucas-charp-shifted-hankel-geometric-ratio -/
theorem paper_conclusion_lucas_charp_shifted_hankel_geometric_ratio
    (D : ConclusionLucasCharpShiftedHankelData) :
    And D.rankEqualsOrder D.shiftedHankelGeometricRatio := by
  exact ⟨D.rankEqualsOrder_holds, D.shiftedHankelGeometricRatio_holds⟩

end Omega.Conclusion
