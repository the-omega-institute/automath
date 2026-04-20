import Mathlib.Tactic
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Concrete data for the fiber/Fibonacci fusion-path bijection. The only external parameter is the
path length `ell`; the independent-set side is the path-independent-set model from
`Omega.Combinatorics.FibonacciCube`, and the fusion-path side is the stable Fibonacci syntax
`Omega.X ell`. -/
structure FiberFibonacciFusionData where
  ell : Nat

/-- Path-independent sets on the length-`ell` path. -/
abbrev FiberFibonacciFusionData.independentSets (D : FiberFibonacciFusionData) : Type :=
  PathIndSets D.ell

/-- Admissible Fibonacci fusion-channel sequences. These are encoded by the stable binary words
with no adjacent `1`s, i.e. by `Omega.X ell`. -/
abbrev FiberFibonacciFusionData.fusionPathBasis (D : FiberFibonacciFusionData) : Type :=
  Omega.X D.ell

/-- Forward map: read the independent set as the positions where the intermediate fusion channel
is the tensor unit. -/
noncomputable def FiberFibonacciFusionData.pathIndSetToFusionPath
    (D : FiberFibonacciFusionData) :
    D.independentSets → D.fusionPathBasis :=
  (xEquivPathIndSet D.ell).symm

/-- Inverse map: recover the independent set by reading off the tensor-unit positions in the
fusion path. -/
noncomputable def FiberFibonacciFusionData.fusionPathToPathIndSet
    (D : FiberFibonacciFusionData) :
    D.fusionPathBasis → D.independentSets :=
  xEquivPathIndSet D.ell

/-- The concrete bijection between path-independent sets and admissible Fibonacci fusion paths. -/
noncomputable def FiberFibonacciFusionData.independentSetsEquivFusionPathBasis
    (D : FiberFibonacciFusionData) :
    D.independentSets ≃ D.fusionPathBasis :=
  (xEquivPathIndSet D.ell).symm

/-- The Fibonacci fusion-path basis cardinality. -/
noncomputable def FiberFibonacciFusionData.fusionPathBasisCard
    (D : FiberFibonacciFusionData) : Nat :=
  Fintype.card D.fusionPathBasis

/-- Path-independent sets on a path are in bijection with admissible Fibonacci fusion-channel
sequences, and both are counted by the Fibonacci number `F_{ell+2}`.
    prop:pom-fiber-fibonacci-anyon-fusion-path-bijection -/
theorem paper_pom_fiber_fibonacci_anyon_fusion_path_bijection
    (D : FiberFibonacciFusionData) :
    Nonempty (D.independentSets ≃ D.fusionPathBasis) ∧
      D.fusionPathBasisCard = Nat.fib (D.ell + 2) := by
  refine ⟨⟨D.independentSetsEquivFusionPathBasis⟩, ?_⟩
  simpa [FiberFibonacciFusionData.fusionPathBasisCard,
    FiberFibonacciFusionData.fusionPathBasis] using Omega.X.card_eq_fib D.ell

end Omega.POM
