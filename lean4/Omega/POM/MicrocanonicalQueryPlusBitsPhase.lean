import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.MicrocanonicalPosteriorModuliCLT
import Omega.POM.MicrocanonicalQueryDistortionStrongConversePlane
import Omega.POM.WitnessExtractionOptimalSuccess

namespace Omega.POM

open scoped BigOperators

/-- Uniform-prior expected recovery success after averaging the exact conditional `min` formula
over the posterior fibers. -/
noncomputable def pom_microcanonical_query_plus_bits_phase_expected_success
    {X : Type} [Fintype X] (posteriorModulus : X → ℕ) (B : ℕ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ *
    ∑ x : X, min (1 : ℝ) (((2 : ℝ) ^ B) / (posteriorModulus x : ℝ))

/-- Critical-window side-information density from the paper's `B_N log 2` normalization. -/
noncomputable def pom_microcanonical_query_plus_bits_phase_critical_bit_density
    (beta H_w V_w : ℝ) : ℝ :=
  ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w) / Real.log 2

/-- Concrete package for `thm:pom-microcanonical-query-plus-bits-phase`: the pointwise optimal
`min` success profile averages to the exact expected success law, and the critical-window
normalization rewrites the success exponent to the Gaussian fluctuation coordinate. -/
def pom_microcanonical_query_plus_bits_phase_statement : Prop :=
  (∀ {X : Type} [Fintype X], ∀ posteriorModulus : X → ℕ,
      (∀ x, 1 ≤ posteriorModulus x) →
      ∀ B : ℕ,
        ∃ Succ : X → ℝ,
          (∀ x, Succ x = min (1 : ℝ) (((2 : ℝ) ^ B) / (posteriorModulus x : ℝ))) ∧
          pom_microcanonical_query_plus_bits_phase_expected_success posteriorModulus B =
            (Fintype.card X : ℝ)⁻¹ * ∑ x : X, Succ x ∧
          (∀ x : X, ∀ eps : ℝ, 0 < eps → eps < 1 → 1 - eps ≤ Succ x →
            (1 - eps) * (posteriorModulus x : ℝ) ≤ (2 : ℝ) ^ B)) ∧
    ∀ beta H_w V_w successExponent : ℝ,
      0 ≤ beta →
      beta < 1 →
      0 ≤ pom_microcanonical_query_plus_bits_phase_critical_bit_density beta H_w V_w →
      successExponent ≤
          min 0
            (pom_microcanonical_query_plus_bits_phase_critical_bit_density beta H_w V_w *
                Real.log 2 -
              (1 - beta) * H_w) →
        min 0
            (pom_microcanonical_query_plus_bits_phase_critical_bit_density beta H_w V_w *
                Real.log 2 -
              (1 - beta) * H_w) ≤
          successExponent →
        successExponent = min 0 (Real.sqrt (beta * (1 - beta)) * V_w)

/-- Paper label: `thm:pom-microcanonical-query-plus-bits-phase`. -/
theorem paper_pom_microcanonical_query_plus_bits_phase :
    pom_microcanonical_query_plus_bits_phase_statement := by
  refine ⟨?_, ?_⟩
  · intro X _ posteriorModulus hPosteriorPos B
    obtain ⟨Succ, hSucc, hBound⟩ :=
      paper_pom_witness_extraction_optimal_success (X := X) posteriorModulus hPosteriorPos B
    refine ⟨Succ, hSucc, ?_, hBound⟩
    simp [pom_microcanonical_query_plus_bits_phase_expected_success, hSucc]
  · intro beta H_w V_w successExponent hBeta0 hBeta1 hBits hUpper hLower
    let bitDensity :=
      pom_microcanonical_query_plus_bits_phase_critical_bit_density beta H_w V_w
    have hLogTwo : Real.log 2 ≠ 0 := by
      have hPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hCritical :
        bitDensity * Real.log 2 =
          (1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w := by
      dsimp [bitDensity, pom_microcanonical_query_plus_bits_phase_critical_bit_density]
      field_simp [hLogTwo]
    have hWindow :=
      paper_pom_microcanonical_query_distortion_strong_converse_plane beta bitDensity H_w
        successExponent hBeta0 hBeta1 hBits hUpper hLower
    calc
      successExponent = min 0 (bitDensity * Real.log 2 - (1 - beta) * H_w) := hWindow
      _ = min 0 (Real.sqrt (beta * (1 - beta)) * V_w) := by
            rw [hCritical]
            ring_nf

end Omega.POM
