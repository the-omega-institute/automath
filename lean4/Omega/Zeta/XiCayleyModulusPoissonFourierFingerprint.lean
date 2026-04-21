import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The explicit Cayley-modulus profile on the vertical line at height `δ`. -/
def xiCayleyModulus (δ ξ : ℝ) : ℝ :=
  Real.log (((1 + δ) ^ 2 + ξ ^ 2) / ((1 - δ) ^ 2 + ξ ^ 2))

/-- Primitive of the Poisson-scale kernel in the scale variable. -/
def xiPoissonWindowPrimitive (ξ s : ℝ) : ℝ :=
  Real.log (s ^ 2 + ξ ^ 2)

/-- Closed-form Poisson window integral over `s ∈ [1 - δ, 1 + δ]`. -/
def xiPoissonWindowIntegral (δ ξ : ℝ) : ℝ :=
  xiPoissonWindowPrimitive ξ (1 + δ) - xiPoissonWindowPrimitive ξ (1 - δ)

/-- The zero-frequency Fourier fingerprint extracted from the Poisson window. -/
def xiFourierFingerprint (δ : ℝ) : ℝ :=
  xiPoissonWindowIntegral δ 0 / 2

/-- Paper-facing statement for the Cayley-modulus/Poisson/Fourier bridge. -/
def XiCayleyModulusPoissonFourierFingerprintStatement (δ : ℝ) : Prop :=
  (∀ ξ, xiCayleyModulus δ ξ = xiPoissonWindowIntegral δ ξ) ∧
    xiCayleyModulus δ 0 = 2 * xiFourierFingerprint δ

/-- Paper label: `thm:xi-cayley-modulus-poisson-fourier-fingerprint`. -/
theorem paper_xi_cayley_modulus_poisson_fourier_fingerprint
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) : XiCayleyModulusPoissonFourierFingerprintStatement δ := by
  have hplus : 0 < 1 + δ := by linarith
  have hminus : 0 < 1 - δ := by linarith
  refine ⟨?_, ?_⟩
  · intro ξ
    unfold xiCayleyModulus xiPoissonWindowIntegral xiPoissonWindowPrimitive
    have hnum : ((1 + δ) ^ 2 + ξ ^ 2) ≠ 0 := by
      have : 0 < (1 + δ) ^ 2 + ξ ^ 2 := by
        have hpos : 0 < (1 + δ) ^ 2 := sq_pos_of_pos hplus
        nlinarith [sq_nonneg ξ]
      linarith
    have hden : ((1 - δ) ^ 2 + ξ ^ 2) ≠ 0 := by
      have : 0 < (1 - δ) ^ 2 + ξ ^ 2 := by
        have hpos : 0 < (1 - δ) ^ 2 := sq_pos_of_pos hminus
        nlinarith [sq_nonneg ξ]
      linarith
    rw [Real.log_div hnum hden]
  · have hrepr : xiCayleyModulus δ 0 = xiPoissonWindowIntegral δ 0 := by
      unfold xiCayleyModulus xiPoissonWindowIntegral xiPoissonWindowPrimitive
      have hnum : ((1 + δ) ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
        have : 0 < (1 + δ) ^ 2 + (0 : ℝ) ^ 2 := by
          have hpos : 0 < (1 + δ) ^ 2 := sq_pos_of_pos hplus
          nlinarith
        linarith
      have hden : ((1 - δ) ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
        have : 0 < (1 - δ) ^ 2 + (0 : ℝ) ^ 2 := by
          have hpos : 0 < (1 - δ) ^ 2 := sq_pos_of_pos hminus
          nlinarith
        linarith
      rw [Real.log_div hnum hden]
    unfold xiFourierFingerprint
    simpa [hrepr] using
      (show xiPoissonWindowIntegral δ 0 = 2 * (xiPoissonWindowIntegral δ 0 / 2) by ring)

end

end Omega.Zeta
