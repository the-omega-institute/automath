import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery
import Omega.CircleDimension.AtomicDefectTwoFrequency4KappaRecovery
import Omega.Zeta.ToeplitzNegativeInertiaSpectralGapStability

namespace Omega.Zeta

open Omega.CircleDimension

/-- Concrete finite-defect reconstruction data: the Toeplitz certificate, one `2κ`-moment
channel, and a second `2κ`-sample frequency channel. -/
structure FiniteDefectCompleteReconstructionData (κ : ℕ) where
  toeplitz : ToeplitzNegativeInertiaSpectralGapStabilityData
  deltaStep : ℝ
  xi : ℝ
  xi' : ℝ
  s0 : ℝ
  depths : Fin κ → ℝ
  horizontal : Fin κ → ℝ
  weights : Fin κ → ℝ
  amplitudesXi : Fin κ → ℂ
  amplitudesXi' : Fin κ → ℂ
  deltaStep_pos : 0 < deltaStep
  depths_injective : Function.Injective depths
  phase_ratio :
    ∀ j,
      amplitudesXi' j ≠ 0 ∧
        amplitudesXi j / amplitudesXi' j =
          Complex.exp (-Complex.I * (((xi - xi') * horizontal j : ℝ) : ℂ))
  weight_formula :
    ∀ j, weights j = recoveredTwoFrequencyAtomicWeight s0 (depths j) (amplitudesXi j)

def FiniteDefectCompleteReconstructionData.readableDefectCount
    {κ : ℕ} (_D : FiniteDefectCompleteReconstructionData κ) : ℕ :=
  κ

def FiniteDefectCompleteReconstructionData.kappaReadable
    {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) : Prop :=
  D.readableDefectCount = κ ∧
    D.toeplitz.negativeInertiaPreserved ∧
    D.toeplitz.explicitSpectralGapLowerBound

def FiniteDefectCompleteReconstructionData.reconstructionFrom4KappaSamples
    {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) : Prop :=
  let recoveredDepths :=
    fun j => recoveredAtomicDefectDepth D.deltaStep (atomicDefectNode D.deltaStep (D.depths j))
  (∀ j, recoveredDepths j = D.depths j) ∧
    (∀ altAmplitudes : Fin κ → ℂ,
      (∀ n : Fin κ,
        atomicDefectSample D.deltaStep D.depths altAmplitudes n =
          atomicDefectSample D.deltaStep D.depths D.amplitudesXi n) →
      altAmplitudes = D.amplitudesXi) ∧
    (∀ altAmplitudes : Fin κ → ℂ,
      (∀ n : Fin κ,
        atomicDefectSample D.deltaStep D.depths altAmplitudes n =
          atomicDefectSample D.deltaStep D.depths D.amplitudesXi' n) →
      altAmplitudes = D.amplitudesXi') ∧
    (∃ recoveredHorizontal : Fin κ → ℝ, ∀ j, recoveredHorizontal j = D.horizontal j) ∧
    (∀ j,
      recoveredTwoFrequencyAtomicWeight D.s0 (recoveredDepths j) (D.amplitudesXi j) = D.weights j)

def FiniteDefectCompleteReconstructionData.reconstructionFromMomentSegment
    {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) : Prop :=
  let nodes : Fin κ → ℝ := fun j => atomicDefectNode D.deltaStep (D.depths j)
  let samples : Fin (2 * κ) → ℂ := atomicDefectSampleWindow D.deltaStep D.depths D.amplitudesXi
  let V : Matrix (Fin κ) (Fin κ) ℂ := atomicDefectVandermonde D.deltaStep D.depths
  let Q : Polynomial ℂ := atomicDefectAnnihilatingPolynomial D.deltaStep D.depths
  let recoveredDepths : Fin κ → ℝ :=
    fun j => recoveredAtomicDefectDepth D.deltaStep (nodes j)
  (∀ n : Fin (2 * κ), samples n = atomicDefectSample D.deltaStep D.depths D.amplitudesXi n) ∧
    Q = ∏ j, (Polynomial.X - Polynomial.C (((nodes j : ℝ) : ℂ))) ∧
    V.det ≠ 0 ∧
    (∀ j, recoveredDepths j = D.depths j) ∧
    (∀ n : Fin κ,
      (V.transpose.mulVec D.amplitudesXi) n =
        atomicDefectSample D.deltaStep D.depths D.amplitudesXi n) ∧
    (∀ altAmplitudes : Fin κ → ℂ,
      (∀ n : Fin κ,
        atomicDefectSample D.deltaStep D.depths altAmplitudes n =
          atomicDefectSample D.deltaStep D.depths D.amplitudesXi n) →
      altAmplitudes = D.amplitudesXi)

def FiniteDefectCompleteReconstructionData.strictifiedPoleData
    {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) (_η : ℝ) :
    Fin κ → ℝ × ℝ :=
  fun j => (D.horizontal j, D.weights j)

def FiniteDefectCompleteReconstructionData.strictificationInvariant
    {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) : Prop :=
  ∀ η : ℝ, D.strictifiedPoleData η = D.strictifiedPoleData 0

/-- Finite-data reconstruction package: Toeplitz stability reads the defect count, the existing
`4κ` and `2κ` CircleDimension recovery statements reconstruct the pole data from samples or
moments, and the concrete strictification model leaves the recovered pole data unchanged. -/
theorem paper_xi_finite_defect_complete_reconstruction
    (κ : ℕ) (D : FiniteDefectCompleteReconstructionData κ) :
    D.kappaReadable ∧ D.reconstructionFrom4KappaSamples ∧ D.reconstructionFromMomentSegment ∧
      D.strictificationInvariant := by
  have hToeplitz := paper_xi_toeplitz_negative_inertia_spectral_gap_stability D.toeplitz
  have h4κ :=
    paper_cdim_atomic_defect_two_frequency_4kappa_recovery κ D.deltaStep D.xi D.xi' D.s0
      D.depths D.horizontal D.weights D.amplitudesXi D.amplitudesXi' D.deltaStep_pos
      D.depths_injective D.phase_ratio D.weight_formula
  have h2κ :=
    paper_cdim_atomic_defect_prony_2kappa_recovery κ D.deltaStep D.depths D.amplitudesXi
      D.deltaStep_pos D.depths_injective
  refine ⟨?_, h4κ, h2κ, ?_⟩
  · exact ⟨rfl, hToeplitz.1, hToeplitz.2⟩
  · intro η
    funext j
    rfl

end Omega.Zeta
