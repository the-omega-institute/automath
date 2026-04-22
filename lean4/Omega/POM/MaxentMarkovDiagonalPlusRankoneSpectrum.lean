import Mathlib.Tactic
import Omega.POM.MaxentMarkovUniqueOptimalKernel

namespace Omega.POM

/-- Paper label: `thm:pom-maxent-markov-diagonal-plus-rankone-spectrum`.

In the one-state audited model, the unique optimal stationary coupling is already of
diagonal-plus-rank-one form, and the resulting scalar symmetrized operator has the expected
secular factorization and unique nonzero spectral root. -/
theorem paper_pom_maxent_markov_diagonal_plus_rankone_spectrum :
    (unique_entropy_maximizer ∧ unique_mutual_information_minimizer ∧ rate_distortion_identity) ∧
      ∃ κ : ℝ, ∃ u : Unit → ℝ,
        (stationaryCouplingOfKernel unitStationaryKernel =
          fun p : Unit × Unit =>
            u p.1 * u p.2 + if p.1 = p.2 then κ * (u p.1) ^ 2 else 0) ∧
          (∀ z : ℝ, z ≠ 0 →
            1 - z =
              (κ * (u ()) ^ 2 - z) * (1 + (u ()) ^ 2 / (κ * (u ()) ^ 2 - z))) ∧
          (∀ z : ℝ, z ≠ 0 →
            (1 + (u ()) ^ 2 / (κ * (u ()) ^ 2 - z) = 0 ↔ z = 1)) := by
  refine ⟨paper_pom_maxent_markov_unique_optimal_kernel, ?_⟩
  refine ⟨0, (fun _ => 1), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · funext p
    rcases p with ⟨x, y⟩
    cases x
    cases y
    simp [stationaryCouplingOfKernel, unitStationaryKernel, unitStationaryWeight]
  · intro z hz
    field_simp [hz]
    ring
  · intro z
    exact fun hz => by
      constructor
      · intro hsec
        have hmul := congrArg (fun x : ℝ => x * (-z)) hsec
        field_simp [hz] at hmul
        linarith
      · intro hroot
        subst hroot
        norm_num

end Omega.POM
