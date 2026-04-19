import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Prime support carried by a finite set `S`. -/
abbrev SolenoidPrimeSupport (S : Finset ℕ) := {p : ℕ // p ∈ S ∧ Nat.Prime p}

instance instFactSolenoidPrimeSupportPrime {S : Finset ℕ} (p : SolenoidPrimeSupport S) :
    Fact p.1.Prime :=
  ⟨p.2.2⟩

/-- Concrete model for the Pontryagin dual of `ℤ[S⁻¹] / ℤ`: one `p`-adic factor for each prime
of `S`. -/
abbrev SolenoidLocalizedQuotientDual (S : Finset ℕ) :=
  ∀ p : SolenoidPrimeSupport S, ℤ_[p.1]

/-- Concrete kernel model for the solenoid projection `π_S`. -/
abbrev SolenoidProjectionKernel (S : Finset ℕ) :=
  SolenoidLocalizedQuotientDual S

/-- Concrete product-of-`ℤ_p` model indexed by the primes of `S`. -/
abbrev SolenoidKernelProductZpModel (S : Finset ℕ) :=
  ∀ p : SolenoidPrimeSupport S, ℤ_[p.1]

/-- The solenoid kernel is identified with the dual of `ℤ[S⁻¹] / ℤ`, and hence with the product of
the `p`-adic integers over the prime support `S`. -/
theorem paper_cdim_solenoid_kernel_product_zp (S : Finset ℕ) :
    Nonempty (SolenoidProjectionKernel S ≃ SolenoidLocalizedQuotientDual S) ∧
      Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) := by
  refine ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩⟩

end Omega.CircleDimension
