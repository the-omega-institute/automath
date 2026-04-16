import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.CircleDimension

open Matrix

/-- The exponential node attached to a defect depth and spacing `Δs`. -/
noncomputable def atomicDefectNode (deltaStep depth : ℝ) : ℝ :=
  Real.exp (-deltaStep * depth)

/-- The complex exponential-sum sample sequence attached to the nodes `exp(-Δs δⱼ)`. -/
noncomputable def atomicDefectSample {κ : ℕ} (deltaStep : ℝ) (depths : Fin κ → ℝ)
    (amplitudes : Fin κ → ℂ)
    (n : ℕ) : ℂ :=
  ∑ j, amplitudes j * ((atomicDefectNode deltaStep (depths j) : ℝ) : ℂ) ^ n

/-- The first `m` Prony samples, packaged as a finite vector. -/
noncomputable def atomicDefectSampleWindow {κ m : ℕ} (deltaStep : ℝ) (depths : Fin κ → ℝ)
    (amplitudes : Fin κ → ℂ) : Fin m → ℂ :=
  fun n => atomicDefectSample deltaStep depths amplitudes n

/-- The Vandermonde matrix attached to the exponential nodes `λⱼ = exp(-Δs δⱼ)`. -/
noncomputable def atomicDefectVandermonde {κ : ℕ} (deltaStep : ℝ) (depths : Fin κ → ℝ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  Matrix.vandermonde fun j => ((atomicDefectNode deltaStep (depths j) : ℝ) : ℂ)

/-- The monic annihilating polynomial with roots `λⱼ = exp(-Δs δⱼ)`. -/
noncomputable def atomicDefectAnnihilatingPolynomial {κ : ℕ} (deltaStep : ℝ)
    (depths : Fin κ → ℝ) : Polynomial ℂ :=
  ∏ j, (Polynomial.X - Polynomial.C (((atomicDefectNode deltaStep (depths j) : ℝ) : ℂ)))

/-- Recover the depth from a positive node by the logarithm formula `δ = -(log λ)/Δs`. -/
noncomputable def recoveredAtomicDefectDepth (deltaStep node : ℝ) : ℝ :=
  -Real.log node / deltaStep

/-- The first `κ` Prony equations are the transpose-Vandermonde system. -/
lemma atomicDefectVandermonde_mulVec {κ : ℕ} (deltaStep : ℝ) (depths : Fin κ → ℝ)
    (amplitudes : Fin κ → ℂ) (n : Fin κ) :
    ((atomicDefectVandermonde deltaStep depths).transpose.mulVec amplitudes) n =
      atomicDefectSample deltaStep depths amplitudes n := by
  simp [atomicDefectVandermonde, atomicDefectSample, Matrix.mulVec, dotProduct,
    Matrix.vandermonde, mul_comm]

/-- Distinct depths yield distinct exponential nodes when `Δs > 0`. -/
lemma atomicDefectNode_injective {κ : ℕ} {deltaStep : ℝ} (hdeltaStep : 0 < deltaStep)
    {depths : Fin κ → ℝ} (hdepths : Function.Injective depths) :
    Function.Injective (fun j => atomicDefectNode deltaStep (depths j)) := by
  intro i j hij
  have hlog : -deltaStep * depths i = -deltaStep * depths j := by
    simpa [atomicDefectNode] using congrArg Real.log hij
  have hdepth_eq : depths i = depths j := by
    nlinarith [hlog, hdeltaStep]
  exact hdepths hdepth_eq

/-- With distinct depths, the Vandermonde system for the first `κ` samples is invertible. -/
lemma atomicDefectVandermonde_det_ne_zero {κ : ℕ} {deltaStep : ℝ} (hdeltaStep : 0 < deltaStep)
    {depths : Fin κ → ℝ} (hdepths : Function.Injective depths) :
    (atomicDefectVandermonde deltaStep depths).det ≠ 0 := by
  have hnodes :
      Function.Injective
        (fun j => (((atomicDefectNode deltaStep (depths j) : ℝ) : ℂ))) := by
    intro i j hij
    apply atomicDefectNode_injective hdeltaStep hdepths
    exact Complex.ofReal_injective hij
  simpa [atomicDefectVandermonde] using
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)

/-- Distinct depths imply the amplitudes are uniquely recovered from the first `κ` samples once
    the nodes are known. -/
lemma atomicDefectAmplitudes_unique {κ : ℕ} {deltaStep : ℝ} (hdeltaStep : 0 < deltaStep)
    {depths : Fin κ → ℝ} (hdepths : Function.Injective depths) (amplitudes : Fin κ → ℂ)
    (altAmplitudes : Fin κ → ℂ)
    (hsamples :
      ∀ n : Fin κ,
        atomicDefectSample deltaStep depths altAmplitudes n =
          atomicDefectSample deltaStep depths amplitudes n) :
    altAmplitudes = amplitudes := by
  let V : Matrix (Fin κ) (Fin κ) ℂ := atomicDefectVandermonde deltaStep depths
  have hVdet : V.det ≠ 0 := by
    simpa [V] using atomicDefectVandermonde_det_ne_zero hdeltaStep hdepths
  letI : Invertible V.det := invertibleOfNonzero hVdet
  letI : Invertible V := Matrix.invertibleOfDetInvertible V
  apply Matrix.mulVec_injective_of_invertible V.transpose
  funext n
  have hsample_n := hsamples n
  simpa [V, atomicDefectVandermonde_mulVec] using hsample_n

/-- Paper-facing constructive Prony package for the atomic defect model:
    the first `2κ` samples come from a `κ`-term exponential sum, the annihilating polynomial is
    explicit, the Vandermonde matrix is invertible, depths are recovered by logarithms, and the
    amplitudes are uniquely determined by the first `κ` equations.
    thm:cdim-atomic-defect-prony-2kappa-recovery -/
theorem paper_cdim_atomic_defect_prony_2kappa_recovery
    (κ : ℕ) (deltaStep : ℝ) (depths : Fin κ → ℝ) (amplitudes : Fin κ → ℂ)
    (hdeltaStep : 0 < deltaStep) (hdepths : Function.Injective depths) :
    let nodes : Fin κ → ℝ := fun j => atomicDefectNode deltaStep (depths j)
    let samples : Fin (2 * κ) → ℂ := atomicDefectSampleWindow deltaStep depths amplitudes
    let V : Matrix (Fin κ) (Fin κ) ℂ := atomicDefectVandermonde deltaStep depths
    let Q : Polynomial ℂ := atomicDefectAnnihilatingPolynomial deltaStep depths
    let recoveredDepths : Fin κ → ℝ := fun j => recoveredAtomicDefectDepth deltaStep (nodes j)
    (∀ n : Fin (2 * κ), samples n = atomicDefectSample deltaStep depths amplitudes n) ∧
      Q = ∏ j, (Polynomial.X - Polynomial.C (((nodes j : ℝ) : ℂ))) ∧
      V.det ≠ 0 ∧
      (∀ j, recoveredDepths j = depths j) ∧
      (∀ n : Fin κ,
        (V.transpose.mulVec amplitudes) n = atomicDefectSample deltaStep depths amplitudes n) ∧
      (∀ altAmplitudes : Fin κ → ℂ,
        (∀ n : Fin κ,
          atomicDefectSample deltaStep depths altAmplitudes n =
            atomicDefectSample deltaStep depths amplitudes n) →
        altAmplitudes = amplitudes) := by
  dsimp
  refine ⟨?_, rfl, atomicDefectVandermonde_det_ne_zero hdeltaStep hdepths, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro j
    unfold recoveredAtomicDefectDepth atomicDefectNode
    have hstep_ne : deltaStep ≠ 0 := ne_of_gt hdeltaStep
    rw [Real.log_exp]
    field_simp [hstep_ne]
  · intro n
    exact atomicDefectVandermonde_mulVec deltaStep depths amplitudes n
  · intro altAmplitudes hsamples
    exact atomicDefectAmplitudes_unique hdeltaStep hdepths amplitudes altAmplitudes hsamples

end Omega.CircleDimension
