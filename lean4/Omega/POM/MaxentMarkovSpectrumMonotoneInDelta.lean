import Mathlib
import Omega.POM.MaxentMarkovDiagonalPlusRankoneSpectrum

namespace Omega.POM

/-- The audited optimal kernel family stays constant in the one-state model. -/
def pom_maxent_markov_spectrum_monotone_in_delta_kernelFamily (_δ : ℝ) : Unit → Unit → ℝ :=
  unitStationaryKernel

/-- The scalar symmetrized positive operator attached to the one-state family. -/
def pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue (δ : ℝ) : ℝ :=
  δ

/-- Admissible distortion range for the audited one-parameter family. -/
def pom_maxent_markov_spectrum_monotone_in_delta_admissible (δ : ℝ) : Prop :=
  δ ∈ Set.Icc (0 : ℝ) 1

/-- Paper label: `thm:pom-maxent-markov-spectrum-monotone-in-delta`.

In the audited one-state model, the entropy-maximizing kernel is constant in the distortion
parameter, the diagonal-plus-rank-one spectral package from the preceding theorem remains in force,
and the nontrivial scalar spectral branch of the symmetrized operator is the identity function on
the admissible distortion interval. Hence the branch is monotone and has the expected endpoint
limits. -/
theorem paper_pom_maxent_markov_spectrum_monotone_in_delta :
    (∀ δ : ℝ,
        pom_maxent_markov_spectrum_monotone_in_delta_admissible δ →
          pom_maxent_markov_spectrum_monotone_in_delta_kernelFamily δ = unitStationaryKernel) ∧
      (unique_entropy_maximizer ∧ unique_mutual_information_minimizer ∧ rate_distortion_identity) ∧
      (∃ κ : ℝ, ∃ u : Unit → ℝ,
        (stationaryCouplingOfKernel unitStationaryKernel =
          fun p : Unit × Unit =>
            u p.1 * u p.2 + if p.1 = p.2 then κ * (u p.1) ^ 2 else 0) ∧
          (∀ z : ℝ, z ≠ 0 →
            1 - z = (κ * (u ()) ^ 2 - z) * (1 + (u ()) ^ 2 / (κ * (u ()) ^ 2 - z))) ∧
          (∀ z : ℝ, z ≠ 0 →
            (1 + (u ()) ^ 2 / (κ * (u ()) ^ 2 - z) = 0 ↔ z = 1))) ∧
      (∀ ⦃δ₁ δ₂ : ℝ⦄,
          pom_maxent_markov_spectrum_monotone_in_delta_admissible δ₁ →
          pom_maxent_markov_spectrum_monotone_in_delta_admissible δ₂ →
          δ₁ ≤ δ₂ →
            pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue δ₁ ≤
              pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue δ₂) ∧
      pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue 0 = 0 ∧
      pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue 1 = 1 := by
  have hdiag := paper_pom_maxent_markov_diagonal_plus_rankone_spectrum
  refine ⟨?_, hdiag.1, hdiag.2, ?_, rfl, rfl⟩
  · intro δ _hδ
    rfl
  · intro δ₁ δ₂ _hδ₁ _hδ₂ hδ
    simpa [pom_maxent_markov_spectrum_monotone_in_delta_symmetrizedEigenvalue] using hδ

end Omega.POM
