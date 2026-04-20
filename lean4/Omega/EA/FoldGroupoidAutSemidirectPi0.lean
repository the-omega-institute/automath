import Mathlib.Tactic
import Omega.EA.Wedderburn
import Omega.OperatorAlgebra.FoldFiberNormalizerWreath

namespace Omega.EA

open Omega.OperatorAlgebra

/-- The audited fold multiplicity profile indexed by the canonical enumeration of `X_m`. -/
def foldGroupoidMultiplicityProfile (m : ℕ) : Fin (Nat.fib (m + 2)) → ℕ :=
  fun i => Omega.cFiberMult (Omega.X.ofNat m i.1)

/-- Concrete semidirect-product and component-group package for the finite fold-groupoid
automorphism proxy attached to the multiplicity profile of `X_m`. The compatible visible
permutations model the component group, while the hidden fiberwise permutations model the inner
block automorphisms. -/
def FoldGroupoidAutSemidirectPi0Statement (m : ℕ) : Prop :=
  let d := foldGroupoidMultiplicityProfile m
  Function.Surjective (visibleProjection d) ∧
    (∀ τ : FoldFiberNormalizer d,
      visibleProjection d τ = visibleIdentity d ↔ τ ∈ fiberwiseAutomorphismKernel d) ∧
    (∀ f : CompatibleVisiblePerm d, visibleProjection d (visibleSection d f) = f) ∧
    Nonempty (FoldFiberNormalizer d ≃ CompatibleVisiblePerm d × HiddenFiberAutomorphisms d) ∧
    Fintype.card (HiddenFiberAutomorphisms d) = ∏ x, Nat.factorial (d x) ∧
    Fintype.card (FoldFiberNormalizer d) =
      Fintype.card (CompatibleVisiblePerm d) * ∏ x, Nat.factorial (d x)

/-- Paper label: `thm:fold-groupoid-aut-semidirect-pi0`. The audited fold-groupoid automorphism
proxy splits as compatible visible block permutations together with independent fiberwise inner
automorphisms, and the visible compatible-permutation factor carries the component-group data. -/
theorem paper_fold_groupoid_aut_semidirect_pi0 (m : ℕ) : FoldGroupoidAutSemidirectPi0Statement m := by
  simpa [FoldGroupoidAutSemidirectPi0Statement, foldGroupoidMultiplicityProfile] using
    (paper_op_algebra_fold_fiber_normalizer_wreath
      (m := Nat.fib (m + 2)) (d := foldGroupoidMultiplicityProfile m))

end Omega.EA
