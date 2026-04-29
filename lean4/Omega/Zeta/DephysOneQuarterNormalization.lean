import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The additive entropy constant left undetermined by integrating the first-law normalization. -/
noncomputable def dephys_one_quarter_normalization_additive_constant (G ħ A S : ℝ) : ℝ :=
  S - A / (4 * G * ħ)

/-- Paper label: `prop:dephys-one-quarter-normalization`. -/
theorem paper_dephys_one_quarter_normalization
    (G ħ κ Ω Φ dM dS dA dJ dQ A S : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hκ : κ ≠ 0)
    (hThermo : dM = (ħ * κ / (2 * Real.pi)) * dS + Ω * dJ + Φ * dQ)
    (hMech : dM = (κ / (8 * Real.pi * G)) * dA + Ω * dJ + Φ * dQ) :
    dS = dA / (4 * G * ħ) ∧
      S = A / (4 * G * ħ) + dephys_one_quarter_normalization_additive_constant G ħ A S := by
  have hcore : (ħ * κ / (2 * Real.pi)) * dS = (κ / (8 * Real.pi * G)) * dA := by
    linarith
  have hscaled :
      (8 * Real.pi * G / κ) * ((ħ * κ / (2 * Real.pi)) * dS) =
        (8 * Real.pi * G / κ) * ((κ / (8 * Real.pi * G)) * dA) := by
    exact congrArg (fun t : ℝ => (8 * Real.pi * G / κ) * t) hcore
  have harea : (4 * G * ħ) * dS = dA := by
    have hscaled' := hscaled
    field_simp [hG, hκ, Real.pi_ne_zero] at hscaled'
    ring_nf at hscaled'
    linarith
  refine ⟨?_, ?_⟩
  · field_simp [hG, hħ]
    simpa [mul_assoc, mul_left_comm, mul_comm] using harea
  · unfold dephys_one_quarter_normalization_additive_constant
    ring

end Omega.Zeta
