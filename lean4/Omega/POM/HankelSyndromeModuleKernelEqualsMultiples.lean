import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction

namespace Omega.POM

/-- Chapter-local wrapper for the truncated Hankel-kernel/multiple-module identification. The
fields record the primitive minimal recurrence data, the divisibility step for kernel vectors, and
the recurrence-vanishing step for truncated multiples; the paper-facing outputs are exactly the
two module inclusions whose conjunction gives the equality. -/
structure HankelSyndromeKernelEqualsMultiplesData where
  primitiveMinimalRecurrence : Prop
  kernelVectorsProduceAnnihilators : Prop
  annihilatorsDivisibleByPrimitiveRecurrence : Prop
  truncatedMultiplesSatisfyRecurrence : Prop
  kernelContainedInMultiples : Prop
  multiplesContainedInKernel : Prop
  primitiveMinimalRecurrence_h : primitiveMinimalRecurrence
  kernelVectorsProduceAnnihilators_h : kernelVectorsProduceAnnihilators
  annihilatorsDivisibleByPrimitiveRecurrence_h :
    annihilatorsDivisibleByPrimitiveRecurrence
  truncatedMultiplesSatisfyRecurrence_h : truncatedMultiplesSatisfyRecurrence
  deriveKernelContainedInMultiples :
    primitiveMinimalRecurrence →
      kernelVectorsProduceAnnihilators →
      annihilatorsDivisibleByPrimitiveRecurrence →
        kernelContainedInMultiples
  deriveMultiplesContainedInKernel :
    primitiveMinimalRecurrence →
      truncatedMultiplesSatisfyRecurrence →
        multiplesContainedInKernel

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the principal-ideal stability of the truncated Hankel syndrome
module.
    thm:pom-hankel-syndrome-module-kernel-equals-multiples -/
theorem paper_pom_hankel_syndrome_module_kernel_equals_multiples
    (D : HankelSyndromeKernelEqualsMultiplesData) :
    D.kernelContainedInMultiples ∧ D.multiplesContainedInKernel := by
  refine ⟨?_, ?_⟩
  · exact D.deriveKernelContainedInMultiples D.primitiveMinimalRecurrence_h
      D.kernelVectorsProduceAnnihilators_h
      D.annihilatorsDivisibleByPrimitiveRecurrence_h
  · exact D.deriveMultiplesContainedInKernel D.primitiveMinimalRecurrence_h
      D.truncatedMultiplesSatisfyRecurrence_h

end Omega.POM
