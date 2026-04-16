import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Omega.Folding.YmAmbiguityShellLowEntropy

namespace Omega.Folding

/-- Paper-facing wrapper for the ambiguity-spectrum law: once the matrix-power
counting step and the unique primitive top-SCC Perron--Frobenius package are in
place, the normalized decay law, the second-gap refinement, positivity of the
decay exponents, and the monotonicity chain all follow.
    thm:Ym-ambiguity-spectrum-law -/
theorem paper_Ym_ambiguity_spectrum_law
    (matrixPowerCount uniquePrimitiveTopSCC perronFrobeniusAsymptotic
      normalizedDecayLaw secondGapRefinement : Prop)
    (ρ ε : ℕ → ℝ)
    (hCount : matrixPowerCount)
    (hTop : uniquePrimitiveTopSCC)
    (hPF :
      matrixPowerCount → uniquePrimitiveTopSCC → perronFrobeniusAsymptotic)
    (hDecay : perronFrobeniusAsymptotic → normalizedDecayLaw)
    (hGap : perronFrobeniusAsymptotic → secondGapRefinement)
    (hρrange : ∀ k, 0 < ρ k ∧ ρ k < 2)
    (hρmono : Antitone ρ)
    (hεdef : ∀ k, ε k = Real.log 2 - Real.log (ρ k)) :
    matrixPowerCount ∧ uniquePrimitiveTopSCC ∧ perronFrobeniusAsymptotic ∧
      normalizedDecayLaw ∧ secondGapRefinement ∧ (∀ k, 0 < ε k) ∧ Monotone ε := by
  have hPF' : perronFrobeniusAsymptotic := hPF hCount hTop
  refine ⟨hCount, hTop, hPF', hDecay hPF', hGap hPF', ?_, ?_⟩
  · intro k
    rw [hεdef k]
    have hlog : Real.log (ρ k) < Real.log 2 :=
      paper_Ym_ambiguity_shell_low_entropy (ρ k) (hρrange k)
    linarith
  · intro i j hij
    rw [hεdef i, hεdef j]
    have hlog : Real.log (ρ j) ≤ Real.log (ρ i) :=
      Real.log_le_log (hρrange j).1 (hρmono hij)
    linarith

end Omega.Folding
