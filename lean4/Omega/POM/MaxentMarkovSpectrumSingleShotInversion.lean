import Omega.POM.MaxentMarkovLaguerreSecularSpectrum

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `thm:pom-maxent-markov-spectrum-single-shot-inversion`. -/
theorem paper_pom_maxent_markov_spectrum_single_shot_inversion
    (κ : ℝ) (hκ : 0 < κ) :
    let t : Fin 1 → ℝ := fun _ => κ + 1
    let P : ℝ → ℝ := fun z => κ + 1 - z
    let Q : ℝ → ℝ := fun z => z * (-1) + κ * P z
    let w : Fin 1 → ℝ := fun _ => 1
    (∀ z : ℝ, Q z = (κ + 1) * (κ - z)) ∧
      (∀ z : ℝ, Q z = 0 ↔ z = κ) ∧
      (∀ x : Fin 1, P (t x) = 0) ∧
      (∑ x : Fin 1, w x = 1) := by
  dsimp
  let D : MaxentMarkovLaguerreSecularSpectrumData := ⟨κ, hκ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    simpa [D, MaxentMarkovLaguerreSecularSpectrumData.secularPolynomial,
      MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomial,
      MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomialDeriv,
      MaxentMarkovLaguerreSecularSpectrumData.pole] using
      pom_maxent_markov_laguerre_secular_spectrum_closed_form D z
  · intro z
    simpa [D, MaxentMarkovLaguerreSecularSpectrumData.secularPolynomial,
      MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomial,
      MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomialDeriv,
      MaxentMarkovLaguerreSecularSpectrumData.pole] using
      pom_maxent_markov_laguerre_secular_spectrum_root_iff D z
  · intro x
    fin_cases x
    simp
  · simp

end Omega.POM
