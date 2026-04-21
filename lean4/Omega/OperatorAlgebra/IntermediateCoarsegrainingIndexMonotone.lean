import Mathlib

namespace Omega.OperatorAlgebra

section

variable {OmegaTy XTy : Type*} [Fintype OmegaTy] [DecidableEq OmegaTy]
  [Fintype XTy] [DecidableEq XTy]

/-- The fold-fiber setoid on the finite sample space. -/
def intermediateCoarsegrainingFoldSetoid (fold : OmegaTy → XTy) : Setoid OmegaTy where
  r a b := fold a = fold b
  iseqv := ⟨by intro a; rfl, by intro a b hab; simpa using hab.symm,
    by intro a b c hab hbc; exact hab.trans hbc⟩

/-- Refinement order on setoids: every `R`-class sits inside an `S`-class. -/
def intermediateCoarsegrainingSetoidLE (R S : Setoid OmegaTy) : Prop :=
  ∀ ⦃a b : OmegaTy⦄, R.r a b → S.r a b

/-- The finite equivalence class of `ω` under the intermediate coarse-graining relation. -/
noncomputable def intermediateCoarsegrainingClass (R : Setoid OmegaTy) (ω : OmegaTy) :
    Finset OmegaTy := by
  classical
  exact Finset.univ.filter fun ω' => R.r ω' ω

/-- Quotient-class cardinality at `ω`. -/
noncomputable def intermediateCoarsegrainingQuotientClassCard (R : Setoid OmegaTy) (ω : OmegaTy) :
    ℕ :=
  (intermediateCoarsegrainingClass R ω).card

/-- In the diagonal finite model, the Watatani index of the corresponding class-averaging
conditional expectation is read off blockwise as the class cardinality. -/
noncomputable def intermediateConditionalExpectationIndex (R : Setoid OmegaTy) (ω : OmegaTy) :
    ℕ :=
  intermediateCoarsegrainingQuotientClassCard R ω

/-- Concrete finite data for comparing two intermediate coarse-grainings between equality and the
fold-fiber partition. -/
structure IntermediateCoarsegrainingIndexData
    (OmegaTy XTy : Type*) [Fintype OmegaTy] [DecidableEq OmegaTy] [Fintype XTy] [DecidableEq XTy]
    where
  fold : OmegaTy → XTy
  fine : Setoid OmegaTy
  coarse : Setoid OmegaTy
  fine_le_fold : intermediateCoarsegrainingSetoidLE fine (intermediateCoarsegrainingFoldSetoid fold)
  coarse_le_fold :
    intermediateCoarsegrainingSetoidLE coarse (intermediateCoarsegrainingFoldSetoid fold)
  fine_le_coarse : intermediateCoarsegrainingSetoidLE fine coarse

namespace IntermediateCoarsegrainingIndexData

/-- The two relations are intermediate fold quotients, their Watatani indices are their quotient
class sizes, and the index is monotone under merging classes. -/
def Holds (D : IntermediateCoarsegrainingIndexData OmegaTy XTy) : Prop :=
  intermediateCoarsegrainingSetoidLE D.fine (intermediateCoarsegrainingFoldSetoid D.fold) ∧
    intermediateCoarsegrainingSetoidLE D.coarse (intermediateCoarsegrainingFoldSetoid D.fold) ∧
    intermediateCoarsegrainingSetoidLE D.fine D.coarse ∧
    (∀ ω,
      intermediateConditionalExpectationIndex D.fine ω =
        intermediateCoarsegrainingQuotientClassCard D.fine ω) ∧
    (∀ ω,
      intermediateConditionalExpectationIndex D.coarse ω =
        intermediateCoarsegrainingQuotientClassCard D.coarse ω) ∧
    ∀ ω,
      intermediateConditionalExpectationIndex D.fine ω ≤
        intermediateConditionalExpectationIndex D.coarse ω

end IntermediateCoarsegrainingIndexData

lemma intermediateCoarsegrainingClass_subset {R S : Setoid OmegaTy}
    (hRS : intermediateCoarsegrainingSetoidLE R S) (ω : OmegaTy) :
    intermediateCoarsegrainingClass R ω ⊆ intermediateCoarsegrainingClass S ω := by
  classical
  intro a ha
  simp [intermediateCoarsegrainingClass] at ha ⊢
  exact hRS ha

/-- Paper label: `prop:op-algebra-intermediate-coarsegraining-index-monotone`.
For finite diagonal algebras, any two intermediate coarse-grainings between equality and the fold
fibers have Watatani indices given by their class sizes, and merging classes can only increase the
index blockwise. -/
theorem paper_op_algebra_intermediate_coarsegraining_index_monotone
    {OmegaTy XTy : Type*} [Fintype OmegaTy] [DecidableEq OmegaTy] [Fintype XTy]
    [DecidableEq XTy] (D : IntermediateCoarsegrainingIndexData OmegaTy XTy) : D.Holds := by
  classical
  refine ⟨D.fine_le_fold, D.coarse_le_fold, D.fine_le_coarse, ?_, ?_, ?_⟩
  · intro ω
    rfl
  · intro ω
    rfl
  · intro ω
    exact Finset.card_le_card (intermediateCoarsegrainingClass_subset D.fine_le_coarse ω)

end

end Omega.OperatorAlgebra
