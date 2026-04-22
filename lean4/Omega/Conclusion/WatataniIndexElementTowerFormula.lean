import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

open scoped BigOperators

namespace Omega.Conclusion

open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

/-- Concrete finite tower data for the Watatani-index tower formula at a chosen base point `z`. -/
structure WatataniTowerData where
  Ω : Type
  Y : Type
  Z : Type
  instFintypeΩ : Fintype Ω
  instDecidableEqΩ : DecidableEq Ω
  instFintypeY : Fintype Y
  instDecidableEqY : DecidableEq Y
  instFintypeZ : Fintype Z
  instDecidableEqZ : DecidableEq Z
  f : Ω → Y
  g : Y → Z
  z : Z
  fiber_nonempty : ∃ y : Y, g y = z

attribute [instance] WatataniTowerData.instFintypeΩ
attribute [instance] WatataniTowerData.instDecidableEqΩ
attribute [instance] WatataniTowerData.instFintypeY
attribute [instance] WatataniTowerData.instDecidableEqY
attribute [instance] WatataniTowerData.instFintypeZ
attribute [instance] WatataniTowerData.instDecidableEqZ

namespace WatataniTowerData

/-- The `g`-fiber above the chosen base point. -/
def baseFiber (D : WatataniTowerData) :=
  foldFiber D.g D.z

/-- The `(g ∘ f)`-fiber above the chosen base point. -/
def compositeFiber (D : WatataniTowerData) :=
  foldFiber (D.g ∘ D.f) D.z

instance (D : WatataniTowerData) : Fintype D.baseFiber := by
  dsimp [WatataniTowerData.baseFiber]
  infer_instance

instance (D : WatataniTowerData) : DecidableEq D.baseFiber := by
  dsimp [WatataniTowerData.baseFiber]
  infer_instance

instance (D : WatataniTowerData) : Fintype D.compositeFiber := by
  dsimp [WatataniTowerData.compositeFiber]
  infer_instance

instance (D : WatataniTowerData) : DecidableEq D.compositeFiber := by
  dsimp [WatataniTowerData.compositeFiber]
  infer_instance

/-- The base Watatani index coefficient, identified with the `g`-fiber multiplicity. -/
def baseIndex (D : WatataniTowerData) : ℚ :=
  foldWatataniIndexElement D.g D.z

/-- The composite Watatani index coefficient, identified with the `(g ∘ f)`-fiber multiplicity. -/
def compositeIndex (D : WatataniTowerData) : ℚ :=
  foldWatataniIndexElement (D.g ∘ D.f) D.z

/-- The average `f`-fiber multiplicity over the `g`-fiber above `z`. -/
def expectedFiberAverage (D : WatataniTowerData) : ℚ :=
  (∑ y : D.baseFiber, (foldWatataniIndexElement D.f y.1 : ℚ)) / D.baseIndex

/-- Partitioning the composite fiber over the `g`-fiber above `z`. -/
def conclusion_watatani_index_element_tower_formula_compositeFiberEquiv
    (D : WatataniTowerData) :
    D.compositeFiber ≃ Σ y : D.baseFiber, foldFiber D.f y.1 where
  toFun ω := ⟨⟨D.f ω.1, ω.2⟩, ⟨ω.1, rfl⟩⟩
  invFun s := by
    refine ⟨s.2.1, ?_⟩
    simpa [Function.comp, s.2.2] using s.1.2
  left_inv ω := by
    cases ω
    rfl
  right_inv s := by
    rcases s with ⟨⟨y, hy⟩, ⟨ω, hω⟩⟩
    cases hω
    rfl

theorem conclusion_watatani_index_element_tower_formula_baseIndex_pos
    (D : WatataniTowerData) : 0 < D.baseIndex := by
  rcases D.fiber_nonempty with ⟨y, hy⟩
  have hcard_pos : 0 < Fintype.card (foldFiber D.g D.z) := by
    exact Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
  unfold baseIndex
  rw [(paper_op_algebra_fold_watatani_index_equals_multiplicity_field D.g).2.2]
  exact_mod_cast hcard_pos

theorem conclusion_watatani_index_element_tower_formula_compositeIndex_eq_sum
    (D : WatataniTowerData) :
    D.compositeIndex = ∑ y : D.baseFiber, (foldWatataniIndexElement D.f y.1 : ℚ) := by
  have hcomp_mult := (paper_op_algebra_fold_watatani_index_equals_multiplicity_field (D.g ∘ D.f)).2.2 D.z
  have hcard_nat :
      Fintype.card (foldFiber (D.g ∘ D.f) D.z) =
        Fintype.card (Σ y : D.baseFiber, foldFiber D.f y.1) := by
    exact Fintype.card_congr
      (conclusion_watatani_index_element_tower_formula_compositeFiberEquiv D)
  have hcard_rat :
      (Fintype.card (foldFiber (D.g ∘ D.f) D.z) : ℚ) =
        Fintype.card (Σ y : D.baseFiber, foldFiber D.f y.1) := by
    exact_mod_cast hcard_nat
  have hsigma_nat :
      Fintype.card (Σ y : D.baseFiber, foldFiber D.f y.1) =
        ∑ y : D.baseFiber, Fintype.card (foldFiber D.f y.1) := by
    simpa using (Fintype.card_sigma (α := fun y : D.baseFiber => foldFiber D.f y.1))
  have hsigma_rat :
      (Fintype.card (Σ y : D.baseFiber, foldFiber D.f y.1) : ℚ) =
        ∑ y : D.baseFiber, (Fintype.card (foldFiber D.f y.1) : ℚ) := by
    exact_mod_cast hsigma_nat
  calc
    D.compositeIndex = Fintype.card (foldFiber (D.g ∘ D.f) D.z) := by
      simpa [compositeIndex] using hcomp_mult
    _ = Fintype.card (Σ y : D.baseFiber, foldFiber D.f y.1) := hcard_rat
    _ = ∑ y : D.baseFiber, (Fintype.card (foldFiber D.f y.1) : ℚ) := hsigma_rat
    _ = ∑ y : D.baseFiber, (foldWatataniIndexElement D.f y.1 : ℚ) := by
      simp [foldWatataniIndexElement, foldWatataniIndexCoefficient]

end WatataniTowerData

/-- Paper label: `thm:conclusion-watatani-index-element-tower-formula`.
The composite Watatani index coefficient is the `g`-fiber size times the average `f`-fiber size
over that `g`-fiber. -/
theorem paper_conclusion_watatani_index_element_tower_formula (D : WatataniTowerData) :
    D.compositeIndex = D.baseIndex * D.expectedFiberAverage := by
  have hsum := D.conclusion_watatani_index_element_tower_formula_compositeIndex_eq_sum
  have hbase_ne : D.baseIndex ≠ 0 := by
    exact ne_of_gt D.conclusion_watatani_index_element_tower_formula_baseIndex_pos
  calc
    D.compositeIndex = ∑ y : D.baseFiber, (foldWatataniIndexElement D.f y.1 : ℚ) := hsum
    _ = D.baseIndex * D.expectedFiberAverage := by
      unfold WatataniTowerData.expectedFiberAverage
      field_simp [hbase_ne]

end Omega.Conclusion
