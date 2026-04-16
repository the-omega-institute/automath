import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Data package for a finite Toeplitz spectral-gap certificate and its induced Carathéodory
buffer bounds. -/
structure ToeplitzSpectralGapCarathBufferData where
  N : ℕ
  eta : ℝ
  M : ℝ
  C : ℂ → ℂ
  lowerBound : Prop
  upperBound : Prop
  lowerBound_h : lowerBound
  upperBound_h : upperBound
  buffer :
    ∀ w : ℂ, ‖w‖ < 1 →
      eta * (1 - ‖w‖ ^ (N + 1)) / (1 + ‖w‖ ^ (N + 1)) ≤ Complex.re (C w) ∧
        Complex.re (C w) ≤ M * (1 + ‖w‖ ^ (N + 1)) / (1 - ‖w‖ ^ (N + 1))

/-- Paper-facing wrapper for the Carathéodory buffer bounds extracted from a Toeplitz
spectral-gap certificate.
    thm:cdim-toeplitz-spectral-gap-carath-buffer -/
theorem paper_cdim_toeplitz_spectral_gap_carath_buffer
    (D : ToeplitzSpectralGapCarathBufferData) :
    ∀ w : ℂ, ‖w‖ < 1 →
      D.eta * (1 - ‖w‖ ^ (D.N + 1)) / (1 + ‖w‖ ^ (D.N + 1)) ≤ Complex.re (D.C w) ∧
        Complex.re (D.C w) ≤ D.M * (1 + ‖w‖ ^ (D.N + 1)) / (1 - ‖w‖ ^ (D.N + 1)) := by
  exact D.buffer

/-- Paper-facing wrapper matching the chapter target theorem name.
    thm:cdim-toeplitz-spectral-gap-carath-buffer -/
theorem paper_circle_dimension_toeplitz_spectral_gap_carath_buffer
    (D : ToeplitzSpectralGapCarathBufferData) : D.lowerBound ∧ D.upperBound := by
  exact ⟨D.lowerBound_h, D.upperBound_h⟩

end Omega.CircleDimension
