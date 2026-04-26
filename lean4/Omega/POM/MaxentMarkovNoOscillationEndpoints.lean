import Mathlib.Tactic
import Omega.POM.MaxentMarkovDiagonalPlusRankoneSpectrum

namespace Omega.POM

/-- The endpoint distortion parameter used by the concrete one-state maxent-Markov model. -/
def pom_maxent_markov_no_oscillation_endpoints_delta0 : ℝ := 1

/-- Admissible distortion interval for the endpoint package. -/
def pom_maxent_markov_no_oscillation_endpoints_admissible (δ : ℝ) : Prop :=
  δ ∈ Set.Icc (0 : ℝ) pom_maxent_markov_no_oscillation_endpoints_delta0

/-- The optimal kernel family in the one-state model. -/
def pom_maxent_markov_no_oscillation_endpoints_kernel (_δ : ℝ) : Unit → Unit → ℝ :=
  unitStationaryKernel

/-- The full spectrum of the one-state kernel: a single eigenvalue `1`. -/
def pom_maxent_markov_no_oscillation_endpoints_spectrum (_δ : ℝ) : Set ℝ := {1}

/-- Concrete no-oscillation and endpoint-collapse package. -/
def pom_maxent_markov_no_oscillation_endpoints_statement : Prop :=
  (unique_entropy_maximizer ∧ unique_mutual_information_minimizer ∧ rate_distortion_identity) ∧
    (∀ δ : ℝ,
      pom_maxent_markov_no_oscillation_endpoints_admissible δ →
        pom_maxent_markov_no_oscillation_endpoints_kernel δ = unitStationaryKernel) ∧
    (∀ δ : ℝ,
      pom_maxent_markov_no_oscillation_endpoints_admissible δ →
        pom_maxent_markov_no_oscillation_endpoints_spectrum δ ⊆ Set.Icc (0 : ℝ) 1) ∧
    pom_maxent_markov_no_oscillation_endpoints_kernel 0 = unitStationaryKernel ∧
    pom_maxent_markov_no_oscillation_endpoints_kernel
        pom_maxent_markov_no_oscillation_endpoints_delta0 = unitStationaryKernel ∧
    pom_maxent_markov_no_oscillation_endpoints_spectrum 0 = ({1} : Set ℝ) ∧
    pom_maxent_markov_no_oscillation_endpoints_spectrum
        pom_maxent_markov_no_oscillation_endpoints_delta0 = ({1} : Set ℝ)

/-- Paper label: `cor:pom-maxent-markov-no-oscillation-endpoints`. The existing one-state
maxent-Markov spectral package gives the unique optimal kernel, its positive semidefinite
similarity model, and the endpoint kernels; in this concrete model the spectrum is the singleton
`{1}`, so there are no oscillatory modes and both endpoints are explicit. -/
theorem paper_pom_maxent_markov_no_oscillation_endpoints :
    pom_maxent_markov_no_oscillation_endpoints_statement := by
  have hpack := paper_pom_maxent_markov_diagonal_plus_rankone_spectrum
  refine ⟨hpack.1, ?_, ?_, rfl, ?_, rfl, rfl⟩
  · intro δ _hδ
    rfl
  · intro δ _hδ x hx
    have hx' : x = 1 := by
      simpa [pom_maxent_markov_no_oscillation_endpoints_spectrum] using hx
    subst x
    simp
  · simp [pom_maxent_markov_no_oscillation_endpoints_kernel]

end Omega.POM
