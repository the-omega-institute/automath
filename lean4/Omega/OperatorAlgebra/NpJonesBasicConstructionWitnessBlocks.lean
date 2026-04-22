import Omega.OperatorAlgebra.FoldBasicConstructionPairGroupoid

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

instance np_jones_basic_construction_witness_blocks_pair_groupoid_fintype
    (fold : Ω → X) (x : X) : Fintype (pairGroupoidArrow fold x) :=
  show Fintype (foldFiber fold x × foldFiber fold x) from inferInstance

/-- The witness multiplicity attached to the fiber over `x`. -/
def np_jones_basic_construction_witness_blocks_witness_multiplicity
    (fold : Ω → X) (x : X) : ℕ :=
  Fintype.card (foldFiber fold x)

/-- Each pair-groupoid fiber is a matrix block of size equal to the witness multiplicity. -/
def np_jones_basic_construction_witness_blocks_block_statement
    (fold : Ω → X) (x : X) : Prop :=
  Nonempty (pairGroupoidArrow fold x ≃ foldFiber fold x × foldFiber fold x) ∧
    Fintype.card (pairGroupoidArrow fold x) =
      np_jones_basic_construction_witness_blocks_witness_multiplicity fold x ^ 2

/-- The direct-sum witness-block package for the fold basic construction. -/
def np_jones_basic_construction_witness_blocks_statement (fold : Ω → X) : Prop :=
  FoldBasicConstructionPairGroupoidStatement fold ∧
    ∀ x : X, np_jones_basic_construction_witness_blocks_block_statement fold x

end

/-- Paper label: `thm:np-jones-basic-construction-witness-blocks`. -/
def paper_np_jones_basic_construction_witness_blocks : Prop := by
  exact
    ∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X] (fold : Ω → X),
      np_jones_basic_construction_witness_blocks_statement fold

theorem np_jones_basic_construction_witness_blocks_certified :
    paper_np_jones_basic_construction_witness_blocks := by
  intro Ω X _ _ _ _ fold
  refine ⟨paper_op_algebra_fold_basic_construction_pair_groupoid fold, ?_⟩
  intro x
  refine ⟨⟨Equiv.refl _⟩, ?_⟩
  simp [pairGroupoidArrow, np_jones_basic_construction_witness_blocks_witness_multiplicity,
    pow_two]

end Omega.OperatorAlgebra
