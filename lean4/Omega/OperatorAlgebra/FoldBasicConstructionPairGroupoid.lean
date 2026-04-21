import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

open scoped BigOperators

namespace Omega.OperatorAlgebra

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

open FoldJonesBasicConstructionDirectsum

/-- The arrows in the pair groupoid of the fiber over `x`. -/
def pairGroupoidArrow (fold : Ω → X) (x : X) :=
  foldFiber fold x × foldFiber fold x

/-- The canonical matrix unit attached to an arrow `(a, b)` of the pair groupoid on the `x`-fiber. -/
def pairGroupoidMatrixUnit (fold : Ω → X) (x : X) (a : pairGroupoidArrow fold x) :
    Matrix (foldFiber fold x) (foldFiber fold x) ℂ :=
  fiberMatrixUnit fold x a.1 a.2

/-- The pair-groupoid matrix units satisfy the usual convolution and adjoint formulas. -/
def pairGroupoidMatrixUnitGeneration (fold : Ω → X) : Prop :=
  (∀ x (a b : pairGroupoidArrow fold x),
      pairGroupoidMatrixUnit fold x a * pairGroupoidMatrixUnit fold x b =
        if a.2 = b.1 then pairGroupoidMatrixUnit fold x (a.1, b.2) else 0) ∧
    ∀ x (a : pairGroupoidArrow fold x),
      Matrix.conjTranspose (pairGroupoidMatrixUnit fold x a) =
        pairGroupoidMatrixUnit fold x (a.2, a.1)

/-- The basic construction is the direct sum of the pair-groupoid blocks on the fibers. -/
def FoldBasicConstructionPairGroupoidStatement (fold : Ω → X) : Prop :=
  directsumMatrixDecomposition fold ∧ pairGroupoidMatrixUnitGeneration fold ∧ depthTwoClosure fold

omit [Fintype X] in
lemma pairGroupoidMatrixUnit_mul (fold : Ω → X) (x : X) (a b : pairGroupoidArrow fold x) :
    pairGroupoidMatrixUnit fold x a * pairGroupoidMatrixUnit fold x b =
      if a.2 = b.1 then pairGroupoidMatrixUnit fold x (a.1, b.2) else 0 := by
  simpa [pairGroupoidMatrixUnit] using fiberMatrixUnit_mul fold x a.1 a.2 b.1 b.2

omit [Fintype Ω] [Fintype X] [DecidableEq X] in
lemma pairGroupoidMatrixUnit_conjTranspose (fold : Ω → X) (x : X) (a : pairGroupoidArrow fold x) :
    Matrix.conjTranspose (pairGroupoidMatrixUnit fold x a) =
      pairGroupoidMatrixUnit fold x (a.2, a.1) := by
  simpa [pairGroupoidMatrixUnit] using fiberMatrixUnit_conjTranspose fold x a.1 a.2

/-- Paper label: `thm:op-algebra-fold-basic-construction-pair-groupoid`. The finite-dimensional
Jones basic construction for a fold decomposes as the direct sum of the fiber blocks, and on each
block the canonical matrix units are exactly the matrix units indexed by arrows `(a, b)` in the
pair groupoid of that fiber. -/
theorem paper_op_algebra_fold_basic_construction_pair_groupoid {Ω X : Type*} [Fintype Ω]
    [DecidableEq Ω] [Fintype X] [DecidableEq X] (fold : Ω → X) :
    FoldBasicConstructionPairGroupoidStatement fold := by
  rcases paper_op_algebra_fold_jones_basic_construction_directsum fold with ⟨hDecomp, _, hDepth⟩
  refine ⟨hDecomp, ?_, hDepth⟩
  refine ⟨?_, ?_⟩
  · intro x a b
    exact pairGroupoidMatrixUnit_mul fold x a b
  · intro x a
    exact pairGroupoidMatrixUnit_conjTranspose fold x a

end

end Omega.OperatorAlgebra
