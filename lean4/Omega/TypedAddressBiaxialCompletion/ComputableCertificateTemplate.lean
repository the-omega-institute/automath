import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete witness package for the typed-address computable certificate template. The Fourier
grid and Hardy projection are finite by construction, the kernel is specified by a rational
numerator/denominator pair, and the Poisson coarse graining records the finite blocks consumed by
the offline verifier. -/
structure ComputableCertificateTemplateData where
  fourierGrid : Finset (ℤ × ℤ)
  hardyModes : Finset ℤ
  kernelNumerator : ℤ
  kernelDenominator : ℕ
  kernelDenominator_pos : 0 < kernelDenominator
  coarseGrainingBlocks : Finset (ℤ × ℤ)
  leftEndpoint : ℚ
  rightEndpoint : ℚ
  intervalOrdered : leftEndpoint ≤ rightEndpoint
  errorBudget : ℚ
  errorBudget_nonneg : 0 ≤ errorBudget

/-- The Fourier witness lives on a finite grid. -/
def ComputableCertificateTemplateData.hasFiniteGrid
    (D : ComputableCertificateTemplateData) : Prop :=
  ∃ n : Nat, D.fourierGrid.card = n

/-- The Hardy witness uses finitely many modes. -/
def ComputableCertificateTemplateData.hasFiniteModeProjection
    (D : ComputableCertificateTemplateData) : Prop :=
  ∃ n : Nat, D.hardyModes.card = n

/-- The kernel is given by an explicit rational number. -/
def ComputableCertificateTemplateData.hasExplicitRationalKernel
    (D : ComputableCertificateTemplateData) : Prop :=
  0 < D.kernelDenominator ∧
    ∃ q : ℚ, q = (D.kernelNumerator : ℚ) / (D.kernelDenominator : ℚ)

/-- The interval audit carries ordered endpoints and a nonnegative budget. -/
def ComputableCertificateTemplateData.hasIntervalErrorBudget
    (D : ComputableCertificateTemplateData) : Prop :=
  D.leftEndpoint ≤ D.rightEndpoint ∧ 0 ≤ D.errorBudget

/-- The offline verifier is the joint package of the finite Fourier/Hardy witnesses, the explicit
rational kernel, the interval budget, and the finite Poisson coarse graining. -/
def ComputableCertificateTemplateData.compilesToOfflineVerifier
    (D : ComputableCertificateTemplateData) : Prop :=
  D.hasFiniteGrid ∧
    D.hasFiniteModeProjection ∧
      D.hasExplicitRationalKernel ∧
        D.hasIntervalErrorBudget ∧
          ∃ n : Nat, D.coarseGrainingBlocks.card = n

/-- Paper-facing computable certificate template: the concrete Fourier, Hardy, rational-kernel,
and Poisson coarse-graining data assemble into a single offline-verifier package.
    prop:typed-address-biaxial-completion-computable-certificate-template -/
theorem paper_typed_address_biaxial_completion_computable_certificate_template
    (D : ComputableCertificateTemplateData) :
    D.hasFiniteGrid ∧ D.hasFiniteModeProjection ∧ D.hasExplicitRationalKernel ∧
      D.hasIntervalErrorBudget ∧ D.compilesToOfflineVerifier := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨D.fourierGrid.card, rfl⟩
  · exact ⟨D.hardyModes.card, rfl⟩
  · exact ⟨D.kernelDenominator_pos, (D.kernelNumerator : ℚ) / (D.kernelDenominator : ℚ), rfl⟩
  · exact ⟨D.intervalOrdered, D.errorBudget_nonneg⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨D.fourierGrid.card, rfl⟩
    · exact ⟨D.hardyModes.card, rfl⟩
    · exact ⟨D.kernelDenominator_pos, (D.kernelNumerator : ℚ) / (D.kernelDenominator : ℚ), rfl⟩
    · exact ⟨D.intervalOrdered, D.errorBudget_nonneg⟩
    · exact ⟨D.coarseGrainingBlocks.card, rfl⟩

end Omega.TypedAddressBiaxialCompletion
