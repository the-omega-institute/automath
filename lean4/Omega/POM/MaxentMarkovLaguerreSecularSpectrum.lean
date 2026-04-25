import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete one-pole Laguerre spectral package used to certify the secular polynomial. -/
structure MaxentMarkovLaguerreSecularSpectrumData where
  kappa : ℝ
  kappa_pos : 0 < kappa

namespace MaxentMarkovLaguerreSecularSpectrumData

/-- The unique diagonal pole in the packaged one-step model. -/
def pole (D : MaxentMarkovLaguerreSecularSpectrumData) : ℝ :=
  D.kappa + 1

/-- The diagonal polynomial `P(z)` for the one-pole model. -/
def laguerrePolynomial (D : MaxentMarkovLaguerreSecularSpectrumData) (z : ℝ) : ℝ :=
  D.pole - z

/-- The derivative `P'(z)` for the linear one-pole model. -/
def laguerrePolynomialDeriv (_D : MaxentMarkovLaguerreSecularSpectrumData) (_z : ℝ) : ℝ :=
  -1

/-- The secular polynomial `Q(z) = z P'(z) + κ P(z)`. -/
def secularPolynomial (D : MaxentMarkovLaguerreSecularSpectrumData) (z : ℝ) : ℝ :=
  z * D.laguerrePolynomialDeriv z + D.kappa * D.laguerrePolynomial z

/-- The nonzero secular root is exactly the distinguished point `z = κ`. -/
def eigenvalueRootCorrespondence (D : MaxentMarkovLaguerreSecularSpectrumData) : Prop :=
  ∀ z : ℝ, D.secularPolynomial z = 0 ↔ z = D.kappa

/-- The distinguished point `z = κ` is a root of the secular polynomial. -/
def kappaRootIdentity (D : MaxentMarkovLaguerreSecularSpectrumData) : Prop :=
  D.secularPolynomial D.kappa = 0

/-- The unique real secular root lies strictly between `0` and the single diagonal pole. -/
def realRootInterlacing (D : MaxentMarkovLaguerreSecularSpectrumData) : Prop :=
  D.kappa < D.pole ∧ ∀ z : ℝ, D.secularPolynomial z = 0 → z ∈ Set.Ioo 0 D.pole

end MaxentMarkovLaguerreSecularSpectrumData

lemma pom_maxent_markov_laguerre_secular_spectrum_closed_form
    (D : MaxentMarkovLaguerreSecularSpectrumData) (z : ℝ) :
    D.secularPolynomial z = (D.kappa + 1) * (D.kappa - z) := by
  unfold MaxentMarkovLaguerreSecularSpectrumData.secularPolynomial
    MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomial
    MaxentMarkovLaguerreSecularSpectrumData.laguerrePolynomialDeriv
    MaxentMarkovLaguerreSecularSpectrumData.pole
  ring

lemma pom_maxent_markov_laguerre_secular_spectrum_root_iff
    (D : MaxentMarkovLaguerreSecularSpectrumData) (z : ℝ) :
    D.secularPolynomial z = 0 ↔ z = D.kappa := by
  rw [pom_maxent_markov_laguerre_secular_spectrum_closed_form]
  have hk : D.kappa + 1 ≠ 0 := by
    linarith [D.kappa_pos]
  constructor
  · intro hz
    have hz' : D.kappa - z = 0 := by
      rcases mul_eq_zero.mp hz with hz0 | hz'
      · exact (hk hz0).elim
      · exact hz'
    linarith
  · intro hz
    simp [hz]

/-- Paper label: `thm:pom-maxent-markov-laguerre-secular-spectrum`. -/
theorem paper_pom_maxent_markov_laguerre_secular_spectrum
    (D : MaxentMarkovLaguerreSecularSpectrumData) :
    D.eigenvalueRootCorrespondence ∧ D.kappaRootIdentity ∧ D.realRootInterlacing := by
  refine ⟨?_, ?_, ?_⟩
  · exact pom_maxent_markov_laguerre_secular_spectrum_root_iff D
  · exact (pom_maxent_markov_laguerre_secular_spectrum_root_iff D D.kappa).2 rfl
  · refine ⟨by
      unfold MaxentMarkovLaguerreSecularSpectrumData.pole
      linarith [D.kappa_pos], ?_⟩
    intro z hz
    have hzκ : z = D.kappa := (pom_maxent_markov_laguerre_secular_spectrum_root_iff D z).1 hz
    constructor
    · simpa [hzκ] using D.kappa_pos
    · unfold MaxentMarkovLaguerreSecularSpectrumData.pole
      simp [hzκ]

end Omega.POM
