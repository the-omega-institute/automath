import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- The unsaved three-term Guth--Maynard frequency template before applying the modular
distribution input to the two nonzero Poisson-frequency residual channels. -/
def gm_trace3_improvement_from_mod_distribution_threeTermBound
    (main residualA residualB : ℝ) : ℝ :=
  main + residualA + residualB

/-- The improved three-term template after each nonzero Poisson-frequency residual receives the
same modular spectral-gap saving. -/
def gm_trace3_improvement_from_mod_distribution_improvedBound
    (main saving baseA baseB : ℝ) : ℝ :=
  main + saving * (baseA + baseB)

/-- A concrete modular spectral-gap input for a family of residual terms: every nonzero
Poisson frequency is bounded by the corresponding unsaved base term times the saving factor. -/
def gm_trace3_improvement_from_mod_distribution_modularResidualInput
    (saving : ℝ) (base residual : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, k ≠ 0 → residual k ≤ saving * base k

/-- Concrete theorem statement for
`thm:gm-trace3-improvement-from-mod-distribution`: applying the modular distribution input to the
two nonzero residual channels propagates the common saving through the three-term frequency bound. -/
def gm_trace3_improvement_from_mod_distribution_statement : Prop :=
  ∀ (main saving : ℝ) (baseA baseB residualA residualB : ℕ → ℝ),
    gm_trace3_improvement_from_mod_distribution_modularResidualInput saving baseA residualA →
      gm_trace3_improvement_from_mod_distribution_modularResidualInput saving baseB residualB →
        gm_trace3_improvement_from_mod_distribution_threeTermBound
            main (residualA 1) (residualB 2) ≤
          gm_trace3_improvement_from_mod_distribution_improvedBound
            main saving (baseA 1) (baseB 2)

/-- Paper label: `thm:gm-trace3-improvement-from-mod-distribution`. The frequencies `1` and `2`
stand in for the nonzero Poisson-frequency residual channels; the modular input gives the
`N^{-2δ}` saving on each channel, and elementary order algebra carries it through the three-term
frequency bound. -/
theorem paper_gm_trace3_improvement_from_mod_distribution :
    gm_trace3_improvement_from_mod_distribution_statement := by
  intro main saving baseA baseB residualA residualB hA hB
  have hA1 : residualA 1 ≤ saving * baseA 1 := hA 1 (by norm_num)
  have hB2 : residualB 2 ≤ saving * baseB 2 := hB 2 (by norm_num)
  dsimp [gm_trace3_improvement_from_mod_distribution_threeTermBound,
    gm_trace3_improvement_from_mod_distribution_improvedBound]
  nlinarith

end Omega.SyncKernelWeighted
