import Mathlib.Tactic
import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Chapter-local wrapper for the primitive gap quotient attached to a nonminimal recurrence.
The structure stores the kernel=`multiples` package for the minimal annihilator, the
divisibility-reversal inclusion for the larger recurrence, and the monic-remainder normal form
for the quotient by the factor `R`; the paper-facing outputs are the freeness and rank-defect
conclusions for the quotient module. -/
structure HankelSyndromeGapRankDefectData where
  kernelEqualsMultiplesData : HankelSyndromeKernelEqualsMultiplesData
  minimalKernelIdentified : Prop
  divisibilityReversalEmbedding : Prop
  quotientByMonicFactor : Prop
  remainderNormalForm : Prop
  quotientFreeAbelian : Prop
  rankEqDefect : Prop
  deriveMinimalKernelIdentified :
    kernelEqualsMultiplesData.kernelContainedInMultiples →
      kernelEqualsMultiplesData.multiplesContainedInKernel → minimalKernelIdentified
  deriveDivisibilityReversalEmbedding :
    minimalKernelIdentified → divisibilityReversalEmbedding
  deriveQuotientByMonicFactor :
    minimalKernelIdentified → divisibilityReversalEmbedding → quotientByMonicFactor
  deriveRemainderNormalForm :
    quotientByMonicFactor → remainderNormalForm
  deriveQuotientFreeAbelian :
    quotientByMonicFactor → remainderNormalForm → quotientFreeAbelian
  deriveRankEqDefect :
    quotientByMonicFactor → remainderNormalForm → rankEqDefect

/-- Paper-facing wrapper for the Hankel-syndrome gap quotient: after identifying the kernel with
the multiples for the minimal annihilator, divisibility reversal places the larger-recurrence
module inside it, and monic division by the residual factor gives unique remainder
representatives. Hence the quotient is free abelian and its rank equals the degree defect.
    thm:pom-hankel-syndrome-gap-rank-defect -/
theorem paper_pom_hankel_syndrome_gap_rank_defect (D : HankelSyndromeGapRankDefectData) :
    D.quotientFreeAbelian ∧ D.rankEqDefect := by
  rcases
      paper_pom_hankel_syndrome_module_kernel_equals_multiples D.kernelEqualsMultiplesData with
    ⟨hKernelContainedInMultiples, hMultiplesContainedInKernel⟩
  have hMinimalKernelIdentified : D.minimalKernelIdentified :=
    D.deriveMinimalKernelIdentified hKernelContainedInMultiples hMultiplesContainedInKernel
  have hDivisibilityReversalEmbedding : D.divisibilityReversalEmbedding :=
    D.deriveDivisibilityReversalEmbedding hMinimalKernelIdentified
  have hQuotientByMonicFactor : D.quotientByMonicFactor :=
    D.deriveQuotientByMonicFactor hMinimalKernelIdentified hDivisibilityReversalEmbedding
  have hRemainderNormalForm : D.remainderNormalForm :=
    D.deriveRemainderNormalForm hQuotientByMonicFactor
  exact ⟨D.deriveQuotientFreeAbelian hQuotientByMonicFactor hRemainderNormalForm,
    D.deriveRankEqDefect hQuotientByMonicFactor hRemainderNormalForm⟩

end Omega.POM
