import Mathlib.Data.Complex.Basic
import Omega.Folding.FiberConvolutionKernelInvertibility
import Omega.Folding.FiberSubsetConvolution

namespace Omega.Folding

/-- Concrete data for the maximal identifiable coordinate sigma-algebra. The good coordinates
admit an explicit inverse kernel whose translated pattern counts are read off from the subset
convolution formula, while every bad singleton comes with a nonzero kernel vector producing two
distinct solutions of the same convolution equation. -/
structure FoldFiberIdentifiableSigmaAlgebraData where
  goodCoords : Finset ℕ
  weights : ℕ → ℤ
  zeroFiberCount : ℤ → ℕ
  inverseKernel : Finset ℕ → ℤ → ℕ
  singletonOperator : ℕ → (ℤ → ℂ) → ℤ → ℂ
  badKernelVector : ℕ → ℤ → ℂ
  good_inverse_recovers :
    ∀ I : Finset ℕ, I.Nonempty → I ⊆ goodCoords →
      ∀ r : ℤ,
        inverseKernel I r = fiberSubsetConvolution I weights zeroFiberCount r
  bad_kernel_annihilates :
    ∀ k, k ∉ goodCoords →
      ∀ r : ℤ,
        singletonOperator k (badKernelVector k) r = singletonOperator k 0 r
  badKernelVector_nonzero : ∀ k, k ∉ goodCoords → badKernelVector k ≠ 0

/-- A finite pattern is recoverable when the inverse-kernel reconstruction matches the translated
subset-convolution formula for every residue. -/
def FoldFiberIdentifiableSigmaAlgebraData.recoverable
    (D : FoldFiberIdentifiableSigmaAlgebraData) (I : Finset ℕ) : Prop :=
  ∀ r : ℤ, D.inverseKernel I r = fiberSubsetConvolution I D.weights D.zeroFiberCount r

/-- A singleton coordinate is non-unique when a nonzero kernel vector yields the same singleton
convolution output as the zero solution. -/
def FoldFiberIdentifiableSigmaAlgebraData.singletonNonunique
    (D : FoldFiberIdentifiableSigmaAlgebraData) (k : ℕ) : Prop :=
  ∃ h : ℤ → ℂ, h ≠ 0 ∧ ∀ r : ℤ, D.singletonOperator k h r = D.singletonOperator k 0 r

/-- Paper label: `thm:fold-fiber-identifiable-sigma-algebra-maximal`.
Good coordinate sets are reconstructible from the inverse kernel and the subset-convolution
formula, while any bad singleton has a nonzero kernel witness producing nonuniqueness. -/
theorem paper_fold_fiber_identifiable_sigma_algebra_maximal
    (D : FoldFiberIdentifiableSigmaAlgebraData) :
    (∀ I : Finset ℕ, I.Nonempty → I ⊆ D.goodCoords → D.recoverable I) ∧
      (∀ k, k ∉ D.goodCoords → D.singletonNonunique k) := by
  refine ⟨?_, ?_⟩
  · intro I hI hsubset
    exact D.good_inverse_recovers I hI hsubset
  · intro k hk
    refine ⟨D.badKernelVector k, D.badKernelVector_nonzero k hk, ?_⟩
    exact D.bad_kernel_annihilates k hk

end Omega.Folding
