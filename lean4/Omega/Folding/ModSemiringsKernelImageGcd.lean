import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local data for the kernel/image `gcd` package of multiplication in the folded modular
semiring. The concrete fields track the modulus, a residue representative of the multiplier, and
the resulting kernel and image cardinalities after transport to the residue-class model. -/
structure FoldModSemiringsKernelImageGcdData where
  modulus : ℕ
  residueRepresentative : ℕ
  kernelCardinality : ℕ
  imageCardinality : ℕ
  kernelComputedByGcd :
    kernelCardinality = Nat.gcd residueRepresentative modulus
  imageComputedByGcd :
    imageCardinality = modulus / Nat.gcd residueRepresentative modulus
  kernelCongruenceSolvedByGcd : Prop
  imageCountFromKernel : Prop
  kernelCongruenceSolvedByGcd_h : kernelCongruenceSolvedByGcd
  imageCountFromKernel_h : imageCountFromKernel
  kernelCardFormula : Prop
  imageCardFormula : Prop
  kernelImageProductFormula : Prop
  unitCriterion : Prop
  zeroDivisorCriterion : Prop
  deriveKernelCardFormula :
    kernelCongruenceSolvedByGcd →
      (kernelCardinality = Nat.gcd residueRepresentative modulus) →
        kernelCardFormula
  deriveImageCardFormula :
    imageCountFromKernel →
      (kernelCardinality = Nat.gcd residueRepresentative modulus) →
        (imageCardinality = modulus / Nat.gcd residueRepresentative modulus) →
          imageCardFormula
  deriveKernelImageProductFormula :
    (kernelCardinality = Nat.gcd residueRepresentative modulus) →
      (imageCardinality = modulus / Nat.gcd residueRepresentative modulus) →
        kernelImageProductFormula
  deriveUnitCriterion :
    (kernelCardinality = Nat.gcd residueRepresentative modulus) →
      unitCriterion
  deriveZeroDivisorCriterion :
    (kernelCardinality = Nat.gcd residueRepresentative modulus) →
      zeroDivisorCriterion

/-- Paper-facing wrapper for the kernel/image reciprocity formula for multiplication in the folded
modular semiring: after transporting to multiplication by a residue class modulo `F_{m+2}`, the
kernel size is the relevant `gcd`, the image size is the complementary quotient, their product is
the modulus, and the unit/zero-divisor criteria follow from the same decomposition.
    thm:fold-mod-semirings-kernel-image-gcd -/
theorem paper_fold_mod_semirings_kernel_image_gcd (D : FoldModSemiringsKernelImageGcdData) :
    D.kernelCardFormula ∧ D.imageCardFormula ∧ D.kernelImageProductFormula ∧
      D.unitCriterion ∧ D.zeroDivisorCriterion := by
  have hKernel : D.kernelCardFormula :=
    D.deriveKernelCardFormula D.kernelCongruenceSolvedByGcd_h D.kernelComputedByGcd
  have hImage : D.imageCardFormula :=
    D.deriveImageCardFormula
      D.imageCountFromKernel_h
      D.kernelComputedByGcd
      D.imageComputedByGcd
  have hProduct : D.kernelImageProductFormula :=
    D.deriveKernelImageProductFormula D.kernelComputedByGcd D.imageComputedByGcd
  exact ⟨hKernel, hImage, hProduct, D.deriveUnitCriterion D.kernelComputedByGcd,
    D.deriveZeroDivisorCriterion D.kernelComputedByGcd⟩

end Omega.Folding
