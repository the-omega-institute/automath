import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- Concrete principal-phase model for the four-point readable-time-word shift. The structure is a
marker only; the spectral data are fixed explicitly below. -/
structure ReadableTimeWordPrincipalPhaseGeneratorData where

namespace ReadableTimeWordPrincipalPhaseGeneratorData

/-- Principal phases for the spectrum of the cyclic four-state shift, chosen in `[-π, π]`. -/
def principalPhase (_D : ReadableTimeWordPrincipalPhaseGeneratorData) (k : Fin 4) : ℝ :=
  if k = 0 then 0 else if k = 1 then Real.pi / 2 else if k = 2 then Real.pi else -(Real.pi / 2)

/-- The unitary spectrum recovered from the principal phases by the map `θ ↦ exp(-iθ)`. -/
def shiftSpectrum (_D : ReadableTimeWordPrincipalPhaseGeneratorData) (k : Fin 4) : ℂ :=
  if k = 0 then 1 else if k = 1 then -Complex.I else if k = 2 then -1 else Complex.I

/-- The generator is a bounded self-adjoint diagonal operator: each spectral value is real and
lies in the principal branch `[-π, π]`. -/
def boundedSelfAdjointGenerator (D : ReadableTimeWordPrincipalPhaseGeneratorData) : Prop :=
  ∀ k, |D.principalPhase k| ≤ Real.pi

/-- Exponentiating the principal-phase generator recovers the discrete unitary spectrum. -/
def exponentialRecoversShift (D : ReadableTimeWordPrincipalPhaseGeneratorData) : Prop :=
  ∀ k, Complex.exp (((-D.principalPhase k : ℝ) : ℂ) * Complex.I) = D.shiftSpectrum k

end ReadableTimeWordPrincipalPhaseGeneratorData

open ReadableTimeWordPrincipalPhaseGeneratorData

/-- Paper label: `prop:cdim-unitary-selfadjoint-log`. -/
theorem paper_cdim_unitary_selfadjoint_log (D : ReadableTimeWordPrincipalPhaseGeneratorData) :
    D.boundedSelfAdjointGenerator ∧ D.exponentialRecoversShift := by
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase, Real.pi_pos.le]
    · have hhalf : Real.pi / 2 ≤ Real.pi := by nlinarith [Real.pi_pos]
      have hpi' : 0 ≤ Real.pi / 2 := by positivity
      simpa [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase, abs_of_nonneg hpi'] using
        hhalf
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase, abs_of_pos Real.pi_pos]
    · have hhalf : Real.pi / 2 ≤ Real.pi := by nlinarith [Real.pi_pos]
      have hpi' : 0 ≤ Real.pi / 2 := by positivity
      simpa [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase, abs_neg, abs_of_nonneg hpi']
        using hhalf
  · intro k
    fin_cases k
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase,
        ReadableTimeWordPrincipalPhaseGeneratorData.shiftSpectrum]
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase,
        ReadableTimeWordPrincipalPhaseGeneratorData.shiftSpectrum]
      simpa using (Complex.exp_mul_I (x := -(Real.pi / 2 : ℝ)))
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase,
        ReadableTimeWordPrincipalPhaseGeneratorData.shiftSpectrum]
      simpa using (Complex.exp_mul_I (x := (-Real.pi : ℝ)))
    · simp [ReadableTimeWordPrincipalPhaseGeneratorData.principalPhase,
        ReadableTimeWordPrincipalPhaseGeneratorData.shiftSpectrum]

end

end Omega.CircleDimension
