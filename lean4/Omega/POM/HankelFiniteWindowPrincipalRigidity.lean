import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Concrete finite-window wrapper for the principal-ideal rigidity of the truncated Hankel kernel.
It reuses the existing minimal-recurrence kernel=`multiples` package, and the paper-facing
conclusion is the same pair of inclusions for the finite window. -/
structure HankelFiniteWindowPrincipalRigidityData where
  kernelData : HankelSyndromeKernelEqualsMultiplesData

namespace HankelFiniteWindowPrincipalRigidityData

/-- Every finite-window kernel vector comes from a multiple of the minimal recurrence. -/
def kernelContainedInMultiples (D : HankelFiniteWindowPrincipalRigidityData) : Prop :=
  D.kernelData.kernelContainedInMultiples

/-- Every truncated multiple of the minimal recurrence lies in the finite-window kernel. -/
def multiplesContainedInKernel (D : HankelFiniteWindowPrincipalRigidityData) : Prop :=
  D.kernelData.multiplesContainedInKernel

end HankelFiniteWindowPrincipalRigidityData

open HankelFiniteWindowPrincipalRigidityData

/-- Paper label: `thm:pom-hankel-finite-window-principal-rigidity`. -/
theorem paper_pom_hankel_finite_window_principal_rigidity
    (D : HankelFiniteWindowPrincipalRigidityData) :
    D.kernelContainedInMultiples ∧ D.multiplesContainedInKernel := by
  simpa [HankelFiniteWindowPrincipalRigidityData.kernelContainedInMultiples,
    HankelFiniteWindowPrincipalRigidityData.multiplesContainedInKernel] using
    paper_pom_hankel_syndrome_module_kernel_equals_multiples D.kernelData

end Omega.POM
