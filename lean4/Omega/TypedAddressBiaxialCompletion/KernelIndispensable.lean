import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- A kernel `p`-component together with the visible addresses it accounts for. -/
structure KernelPrimeComponent where
  prime : ℕ
  support : Finset ℕ
deriving DecidableEq

/-- The visible quotient can only forget prime-support information. -/
def visibleQuotientCollapsesPrimeSupport (visibleQuotient primeSupport : Finset ℕ) : Prop :=
  visibleQuotient ⊆ primeSupport

/-- A kernel prime-support decomposition is indispensable when every component lies over the
visible quotient and the recovery map reconstructs the full support. -/
def kernelRecoversPrimeSupport
    (kernelDecomposition : Finset KernelPrimeComponent)
    (recover : Finset KernelPrimeComponent → Finset ℕ)
    (visibleQuotient primeSupport : Finset ℕ) : Prop :=
  (∀ component ∈ kernelDecomposition, component.support ⊆ visibleQuotient) ∧
    recover kernelDecomposition = primeSupport

/-- Packaging of `prop:typed-address-biaxial-completion-kernel-indispensable`: quotient collapse
forgets only the hidden support data, while the kernel prime-support decomposition recovers that
support from its `p`-components. -/
theorem paper_typed_address_biaxial_completion_kernel_indispensable
    (visibleQuotient primeSupport : Finset ℕ)
    (kernelDecomposition : Finset KernelPrimeComponent)
    (recover : Finset KernelPrimeComponent → Finset ℕ)
    (hCollapse : visibleQuotientCollapsesPrimeSupport visibleQuotient primeSupport)
    (hDecomposition :
      ∀ component ∈ kernelDecomposition, component.support ⊆ visibleQuotient)
    (hRecover : recover kernelDecomposition = primeSupport) :
    visibleQuotientCollapsesPrimeSupport visibleQuotient primeSupport ∧
      kernelRecoversPrimeSupport kernelDecomposition recover visibleQuotient primeSupport := by
  exact ⟨hCollapse, ⟨hDecomposition, hRecover⟩⟩

end Omega.TypedAddressBiaxialCompletion
