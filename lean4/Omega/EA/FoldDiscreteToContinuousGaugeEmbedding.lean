import Mathlib.GroupTheory.Perm.Basic
import Omega.EA.FoldGroupoidAutSemidirectPi0

namespace Omega.EA

open Omega.OperatorAlgebra

/-- The discrete fold gauge group is the kernel of the visible projection in the normalizer proxy;
equivalently, it is the product of the fiberwise permutation groups. -/
def FoldDiscreteGaugeGroup {m : ℕ} (d : Fin m → ℕ) :=
  {τ : FoldFiberNormalizer d // visibleProjection d τ = visibleIdentity d}

/-- The continuous proxy acts blockwise on the disjoint union of all fold fibers. -/
abbrev FoldContinuousGaugeProxy {m : ℕ} (d : Fin m → ℕ) :=
  Equiv.Perm (Σ x : Fin m, Fin (d x))

/-- Forget the trivial visible component of a discrete gauge element and keep only the fiberwise
permutations. -/
def foldDiscreteGaugeEquivFiberwise {m : ℕ} (d : Fin m → ℕ) :
    FoldDiscreteGaugeGroup d ≃ HiddenFiberAutomorphisms d where
  toFun τ := τ.1.2
  invFun σ := ⟨(visibleIdentity d, σ), rfl⟩
  left_inv τ := by
    rcases τ with ⟨⟨f, σ⟩, hτ⟩
    dsimp [visibleProjection, visibleIdentity] at hτ
    cases hτ
    rfl
  right_inv σ := rfl

/-- A fiberwise permutation acts blockwise on the ambient disjoint union of fiber labels. -/
def fiberwiseBlockPermutation {m : ℕ} (d : Fin m → ℕ) (σ : HiddenFiberAutomorphisms d) :
    FoldContinuousGaugeProxy d where
  toFun s := ⟨s.1, σ s.1 s.2⟩
  invFun s := ⟨s.1, (σ s.1).symm s.2⟩
  left_inv s := by
    rcases s with ⟨x, i⟩
    simp
  right_inv s := by
    rcases s with ⟨x, i⟩
    simp

/-- The block action is faithful: equality of the induced block permutations implies equality of
the underlying fiberwise permutations. -/
theorem fiberwiseBlockPermutation_injective {m : ℕ} (d : Fin m → ℕ) :
    Function.Injective (fiberwiseBlockPermutation d) := by
  intro σ τ hστ
  funext x
  apply Equiv.ext
  intro i
  have hpoint :=
    congrArg (fun e : FoldContinuousGaugeProxy d => e ⟨x, i⟩) hστ
  simpa [fiberwiseBlockPermutation] using hpoint

/-- The natural embedding of the discrete fold gauge group into the continuous block-permutation
proxy. -/
def foldDiscreteToContinuousGaugeEmbedding {m : ℕ} (d : Fin m → ℕ) :
    FoldDiscreteGaugeGroup d ↪ FoldContinuousGaugeProxy d where
  toFun τ := fiberwiseBlockPermutation d (foldDiscreteGaugeEquivFiberwise d τ)
  inj' := by
    intro τ₁ τ₂ h
    apply (foldDiscreteGaugeEquivFiberwise d).injective
    exact fiberwiseBlockPermutation_injective d h

/-- Paper-facing proposition: the discrete fold gauge group is identified with the product of the
fiberwise symmetric groups, and it embeds faithfully into the blockwise continuous automorphism
proxy. -/
def FoldDiscreteToContinuousGaugeEmbeddingStatement (m : ℕ) : Prop :=
  let d := foldGroupoidMultiplicityProfile m
  Nonempty (FoldDiscreteGaugeGroup d ≃ HiddenFiberAutomorphisms d) ∧
    Nonempty (FoldDiscreteGaugeGroup d ↪ FoldContinuousGaugeProxy d)

/-- Paper label: `prop:fold-discrete-to-continuous-gauge-embedding`. The fold-groupoid
multiplicity profile packages the discrete gauge group as the kernel of the visible normalizer
projection, hence as a product of fiberwise symmetric groups, and the resulting block action on
the disjoint union of all fibers is faithful. -/
theorem paper_fold_discrete_to_continuous_gauge_embedding (m : ℕ) :
    FoldDiscreteToContinuousGaugeEmbeddingStatement m := by
  refine ⟨⟨foldDiscreteGaugeEquivFiberwise (foldGroupoidMultiplicityProfile m)⟩,
    ⟨foldDiscreteToContinuousGaugeEmbedding (foldGroupoidMultiplicityProfile m)⟩⟩

end Omega.EA
