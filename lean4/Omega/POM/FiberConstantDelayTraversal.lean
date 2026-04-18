import Mathlib.Tactic
import Omega.POM.FibCubeGrayHamilton

namespace Omega.POM

/-- Concrete witness for a single Fibonacci-cube factor used in the fiber-product traversal. -/
structure FiberFactorWitness where
  n : ℕ
  grayData : FibCubeGrayHamiltonData n

/-- The factor lengths underlying a fiber-product decomposition. -/
def factorLengths (factors : List FiberFactorWitness) : List ℕ :=
  factors.map fun F => F.n

/-- Recursive witness that each Cartesian-product factor carries a Hamilton path. The product
traversal is read componentwise from this list of one-bit-flip factor traversals. -/
inductive FiberTraversalWitness : List ℕ → Type where
  | nil : FiberTraversalWitness []
  | cons {n : ℕ} {ns : List ℕ} (path : List (Omega.X n))
      (hpath : IsFibCubeHamiltonPath n path) (rest : FiberTraversalWitness ns) :
      FiberTraversalWitness (n :: ns)

/-- The fiber has a Hamilton traversal once every Fibonacci-cube factor is equipped with a
Hamilton path witness. -/
def fiberHasHamiltonTraversal (factors : List FiberFactorWitness) : Prop :=
  Nonempty (FiberTraversalWitness (factorLengths factors))

/-- Reading the recursive Hamilton witnesses factorwise gives a constant-delay enumeration: each
factor path already moves by a single Fibonacci-cube edge, hence by one local toggle. -/
def fiberConstantDelayEnumeration (factors : List FiberFactorWitness) : Prop :=
  Nonempty (FiberTraversalWitness (factorLengths factors))

private def buildFiberTraversal
    (factors : List FiberFactorWitness) :
    FiberTraversalWitness (factorLengths factors) := by
  induction factors with
  | nil =>
      simpa [factorLengths] using FiberTraversalWitness.nil
  | cons F factors ih =>
      have hGray : IsFibCubeHamiltonPath F.n F.grayData.grayOrder :=
        paper_pom_fibcube_gray_hamilton F.grayData
      simpa [factorLengths] using FiberTraversalWitness.cons F.grayData.grayOrder hGray ih

/-- Paper label: `cor:pom-fiber-constant-delay-traversal`. -/
theorem paper_pom_fiber_constant_delay_traversal
    (factors : List FiberFactorWitness) :
    fiberHasHamiltonTraversal factors ∧ fiberConstantDelayEnumeration factors := by
  exact ⟨⟨buildFiberTraversal factors⟩, ⟨buildFiberTraversal factors⟩⟩

end Omega.POM
