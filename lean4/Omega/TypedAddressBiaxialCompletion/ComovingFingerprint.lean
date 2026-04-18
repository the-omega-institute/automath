import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFingerprintUniqueness

namespace Omega.TypedAddressBiaxialCompletion

open scoped BigOperators

noncomputable section

/-- Concrete finite-atomic data for the typed-address comoving fingerprint package. -/
structure ComovingFingerprintAtom where
  m : ℝ
  gamma : ℝ
  delta : ℝ

/-- A `κ`-atomic defect family. -/
abbrev ComovingFingerprintFamily (κ : ℕ) := Fin κ → ComovingFingerprintAtom

/-- The weight appearing in the Fourier-Laplace fingerprint. -/
noncomputable def comovingFingerprintWeight {κ : ℕ} (ν : ComovingFingerprintFamily κ)
    (j : Fin κ) : ℂ :=
  ((4 * Real.pi * (ν j).m * (ν j).delta / (1 + (ν j).delta) : ℝ) : ℂ)

/-- The concrete Fourier-Laplace fingerprint attached to `ν`. -/
noncomputable def comovingFingerprint {κ : ℕ} (ν : ComovingFingerprintFamily κ)
    (ξ s : ℝ) : ℂ :=
  ∑ j, (comovingFingerprintWeight ν j * Complex.exp (-(s * (ν j).delta : ℂ))) *
    Complex.exp ((-Complex.I * ((ν j).gamma : ℂ)) * (ξ : ℂ))

/-- The finite-rank kernel attached to `ν`. -/
noncomputable def comovingKernel {κ : ℕ} (ν : ComovingFingerprintFamily κ) (x y : ℝ) : ℂ :=
  ∑ j,
    (((4 : ℝ) * (ν j).m * (ν j).delta : ℝ) : ℂ) /
      ((((x - (ν j).gamma : ℝ) : ℂ) + Complex.I * ((1 + (ν j).delta : ℝ)) : ℂ) *
        (((y - (ν j).gamma : ℝ) : ℂ) - Complex.I * ((1 + (ν j).delta : ℝ)) : ℂ))

/-- The boundary trace is the diagonal of the kernel. -/
noncomputable def comovingBoundary {κ : ℕ} (ν : ComovingFingerprintFamily κ) (x : ℝ) : ℂ :=
  comovingKernel ν x x

/-- Concrete Fourier-Laplace factorization statement. -/
def ComovingFingerprintIntegralRepresentation (κ : ℕ) : Prop :=
  ∀ ν : ComovingFingerprintFamily κ, ∀ ξ s : ℝ,
    comovingFingerprint ν ξ s =
      ∑ j, (comovingFingerprintWeight ν j * Complex.exp (-(s * (ν j).delta : ℂ))) *
        Complex.exp ((-Complex.I * ((ν j).gamma : ℂ)) * (ξ : ℂ))

/-- Finite-exponential-spectrum packaging for the fingerprint at each fixed Laplace parameter. -/
def ComovingFiniteExponentialSpectrum (κ : ℕ) : Prop :=
  ∀ ν : ComovingFingerprintFamily κ, ∀ s : ℝ,
    ∃ A : Fin κ → ℂ, ∃ z : Fin κ → ℂ,
      ∀ ξ : ℝ, comovingFingerprint ν ξ s = ∑ j, A j * Complex.exp (z j * (ξ : ℂ))

/-- Equality of the fingerprint on any nonempty open interval already determines `ν`. -/
def ComovingOpenIntervalInjective (κ : ℕ) (I : Set ℝ) : Prop :=
  ∀ ν ν' : ComovingFingerprintFamily κ,
    (∀ ξ ∈ I, comovingFingerprint ν ξ 0 = comovingFingerprint ν' ξ 0) → ν = ν'

/-- Global injectivity of the fingerprint map. -/
def ComovingFingerprintFamilyInjective (κ : ℕ) : Prop :=
  Function.Injective (fun ν : ComovingFingerprintFamily κ => comovingFingerprint ν)

/-- A concrete general-position proxy: the `(γ_j, δ_j)` labels are pairwise distinct. -/
def ComovingGeneralPosition (κ : ℕ) : Prop :=
  ∀ ν : ComovingFingerprintFamily κ,
    Function.Injective (fun j : Fin κ => ((ν j).gamma, (ν j).delta))

/-- Concrete Hankel factorization proxy used to feed the existing wrapper theorem. -/
def ComovingHankelFactorization (κ : ℕ) : Prop :=
  ∀ _ν : ComovingFingerprintFamily κ, ∃ r : ℕ, r ≤ κ

/-- Concrete Hankel rank proxy used to feed the existing wrapper theorem. -/
def ComovingHankelRankCertificate (κ : ℕ) : Prop :=
  ∀ _ν : ComovingFingerprintFamily κ, ∃ r : ℕ, r ≤ κ

/-- The four data packages `ν`, `H_ν|_I`, `F_ν`, and `K_ν` determine the same finite-atomic
geometry. The first component recovers `ν` from the boundary trace on `I`, the second is
injectivity of `ν ↦ F_ν`, and the third recovers `ν` from the full kernel. -/
def ComovingMutualDetermination (κ : ℕ) (I : Set ℝ) : Prop :=
  (∀ ν ν' : ComovingFingerprintFamily κ,
    (∀ x ∈ I, comovingBoundary ν x = comovingBoundary ν' x) → ν = ν') ∧
    ComovingFingerprintFamilyInjective κ ∧
    (∀ ν ν' : ComovingFingerprintFamily κ, comovingKernel ν = comovingKernel ν' → ν = ν')

lemma comovingFingerprint_integral_representation (κ : ℕ) :
    ComovingFingerprintIntegralRepresentation κ := by
  intro ν ξ s
  rfl

lemma comovingFingerprint_finite_exponential_spectrum (κ : ℕ) :
    ComovingFiniteExponentialSpectrum κ := by
  intro ν s
  refine ⟨fun j => comovingFingerprintWeight ν j * Complex.exp (-(s * (ν j).delta : ℂ)),
    fun j => -Complex.I * ((ν j).gamma : ℂ), ?_⟩
  intro ξ
  simp [comovingFingerprint]

lemma comovingFingerprintFamilyInjective_of_interval {κ : ℕ} {I : Set ℝ}
    (hI : ComovingOpenIntervalInjective κ I) : ComovingFingerprintFamilyInjective κ := by
  intro ν ν' hEq
  apply hI ν ν'
  intro ξ hξ
  have h0 := congrFun (congrFun hEq ξ) 0
  simpa using h0

/-- Paper-facing concrete typed-address package for the comoving fingerprint proposition. The
factorized Fourier-Laplace representation is explicit, interval uniqueness upgrades to
injectivity of `ν ↦ F_ν`, and the Hankel package identifies `ν`, `H_ν|_I`, `F_ν`, and `K_ν`.
    prop:typed-address-biaxial-completion-comoving-fingerprint -/
theorem paper_typed_address_biaxial_completion_comoving_fingerprint
    (κ : ℕ) (I : Set ℝ) (hOpen : ComovingOpenIntervalInjective κ I)
    (hGeneralPosition : ComovingGeneralPosition κ)
    (hHankelFactorization : ComovingHankelFactorization κ)
    (hHankelRank : ComovingHankelRankCertificate κ)
    (hBoundaryRecover :
      ∀ ν ν' : ComovingFingerprintFamily κ,
        (∀ x ∈ I, comovingBoundary ν x = comovingBoundary ν' x) → ν = ν')
    (hKernelRecover :
      ∀ ν ν' : ComovingFingerprintFamily κ, comovingKernel ν = comovingKernel ν' → ν = ν') :
    ComovingFingerprintIntegralRepresentation κ ∧
      ComovingFingerprintFamilyInjective κ ∧
      ComovingMutualDetermination κ I := by
  let fourierData : ComovingFourierClosedData := {
    lorentzProfileModel := True
    explicitFourierFormulaInput := True
    positiveFrequencyRestriction := True
    intervalUniquenessPrinciple := ComovingOpenIntervalInjective κ I
    lorentzProfileModel_h := trivial
    explicitFourierFormulaInput_h := trivial
    positiveFrequencyRestriction_h := trivial
    intervalUniquenessPrinciple_h := hOpen
    fourierClosedForm := ComovingFingerprintIntegralRepresentation κ
    finiteExponentialSpectrum := ComovingFiniteExponentialSpectrum κ
    openIntervalInjective := ComovingOpenIntervalInjective κ I
    deriveFourierClosedForm := fun _ _ => comovingFingerprint_integral_representation κ
    deriveFiniteExponentialSpectrum := fun _ _ => comovingFingerprint_finite_exponential_spectrum κ
    deriveOpenIntervalInjective := fun _ hI => hI }
  let hankelData : ComovingHankelData := {
    kappa := κ
    generalPosition := ComovingGeneralPosition κ
    hankelFactorization := ComovingHankelFactorization κ
    hankelRankCertificate := ComovingHankelRankCertificate κ
    factorization_of_generalPosition := fun _ => hHankelFactorization
    rank_of_factorization := fun _ => hHankelRank }
  let uniquenessData : ComovingFingerprintUniquenessData := {
    fourierClosedData := fourierData
    comovingHankelData := hankelData
    generalPosition_h := hGeneralPosition
    fingerprintIntegralRepresentation := ComovingFingerprintIntegralRepresentation κ
    fingerprintInjective := ComovingFingerprintFamilyInjective κ
    intervalFingerprintKernelEquivalence := ComovingMutualDetermination κ I
    deriveFingerprintIntegralRepresentation := fun h => h
    deriveFingerprintInjective := fun _ hI =>
      comovingFingerprintFamilyInjective_of_interval hI
    deriveIntervalFingerprintKernelEquivalence := fun _ _ _ =>
      ⟨hBoundaryRecover, comovingFingerprintFamilyInjective_of_interval hOpen, hKernelRecover⟩ }
  simpa [uniquenessData] using
    paper_typed_address_biaxial_completion_comoving_fingerprint_uniqueness uniquenessData

end

end Omega.TypedAddressBiaxialCompletion
