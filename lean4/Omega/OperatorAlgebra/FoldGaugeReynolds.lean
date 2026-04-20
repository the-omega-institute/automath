import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectation
import Omega.OperatorAlgebra.FoldGaugeGroupStructure
import Omega.OperatorAlgebra.FoldInvariantSubalgebra

namespace Omega.OperatorAlgebra

open FoldConditionalExpectationData

/-- Concrete data for the fold-gauge/Reynolds comparison. It packages the fiberwise symmetric-group
decomposition, the invariant-subalgebra package, and the explicit fold conditional expectation. -/
structure FoldGaugeReynoldsData where
  groupData : FoldGaugeGroupStructureData
  invariantData : FoldInvariantSubalgebraData
  expectationData : FoldConditionalExpectationData

namespace FoldGaugeReynoldsData

/-- Fiberwise product decomposition of the fold-gauge group. -/
def groupProductDecomposition (D : FoldGaugeReynoldsData) : Prop :=
  D.groupData.groupStructurePackage

/-- Fixed-point characterization of the fold-invariant subalgebra. -/
def fixedPointSubalgebra (D : FoldGaugeReynoldsData) : Prop :=
  D.invariantData.orthogonalProjectionFamily ∧ D.invariantData.partitionOfUnity ∧
    D.invariantData.invariantSubalgebraIso ∧ D.invariantData.fiberwiseConstantCharacterization

/-- Basis projection in the diagonal finite algebra. -/
def basisProjection (D : FoldGaugeReynoldsData) (a : D.expectationData.Ω) :
    D.expectationData.Ω → ℚ :=
  fun b => if b = a then 1 else 0

/-- Reynolds average of a basis projection along the fold fiber through `a`. -/
def reynoldsAverageOnBasisProjection (D : FoldGaugeReynoldsData) (a : D.expectationData.Ω) :
    D.expectationData.Ω → ℚ :=
  fun b =>
    if D.expectationData.fold b = D.expectationData.fold a then
      1 / D.expectationData.fiberCard (D.expectationData.fold a)
    else 0

lemma reynoldsAverageOnBasisProjection_eq_foldExpectation (D : FoldGaugeReynoldsData)
    (a : D.expectationData.Ω) :
    D.reynoldsAverageOnBasisProjection a =
      D.expectationData.foldExpectation (D.basisProjection a) := by
  classical
  funext b
  by_cases hfold : D.expectationData.fold b = D.expectationData.fold a
  · have ha_mem : a ∈ D.expectationData.fiber (D.expectationData.fold b) := by
      simpa [hfold] using D.expectationData.mem_fiber_self a
    have hsum :
        Finset.sum (D.expectationData.fiber (D.expectationData.fold b)) (D.basisProjection a) = 1 := by
      rw [Finset.sum_eq_single a]
      · simp [basisProjection]
      · intro c hc hca
        simp [basisProjection, hca]
      · intro ha_not_mem
        exact (ha_not_mem ha_mem).elim
    have hcard :
        D.expectationData.fiberCard (D.expectationData.fold b) =
          D.expectationData.fiberCard (D.expectationData.fold a) := by
      simpa [hfold]
    have hself : a ∈ D.expectationData.fiber (D.expectationData.fold a) :=
      D.expectationData.mem_fiber_self a
    rw [reynoldsAverageOnBasisProjection]
    simp [hfold]
    rw [FoldConditionalExpectationData.foldExpectation, hsum]
    simp [basisProjection, hself, hcard]
  · have ha_not_mem : a ∉ D.expectationData.fiber (D.expectationData.fold b) := by
      intro ha_mem
      have : D.expectationData.fold a = D.expectationData.fold b := by
        simpa [FoldConditionalExpectationData.fiber] using ha_mem
      exact hfold this.symm
    have hsum :
        Finset.sum (D.expectationData.fiber (D.expectationData.fold b)) (D.basisProjection a) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro c hc
      by_cases hca : c = a
      · subst hca
        exact (ha_not_mem hc).elim
      · simp [basisProjection, hca]
    rw [reynoldsAverageOnBasisProjection]
    simp [hfold]
    rw [FoldConditionalExpectationData.foldExpectation, hsum]
    simp [basisProjection, ha_not_mem]

/-- Reynolds averaging on basis projections coincides with the explicit fold conditional
expectation, together with the positivity/unitality/idempotence package. -/
def reynoldsEqualsConditionalExpectation (D : FoldGaugeReynoldsData) : Prop :=
  (∀ a, D.reynoldsAverageOnBasisProjection a =
    D.expectationData.foldExpectation (D.basisProjection a)) ∧
    D.expectationData.positiveUnitalIdempotent ∧ D.expectationData.identityOnInvariantSubalgebra ∧
      D.expectationData.bimoduleLaw

end FoldGaugeReynoldsData

open FoldGaugeReynoldsData

/-- Paper label: `prop:fold-gauge-reynolds`. -/
theorem paper_fold_gauge_reynolds (D : FoldGaugeReynoldsData) :
    D.groupProductDecomposition ∧ D.fixedPointSubalgebra ∧ D.reynoldsEqualsConditionalExpectation := by
  have hCond := paper_op_algebra_fold_conditional_expectation D.expectationData
  refine ⟨paper_op_algebra_fold_gauge_group_structure D.groupData,
    paper_op_algebra_fold_invariant_subalgebra D.invariantData, ?_⟩
  rcases hCond with ⟨hPos, hInv, hBimod⟩
  exact ⟨fun a => D.reynoldsAverageOnBasisProjection_eq_foldExpectation a, hPos, hInv, hBimod⟩

end Omega.OperatorAlgebra
