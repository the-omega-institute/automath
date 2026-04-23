import Mathlib.Tactic
import Omega.POM.MaxentMarkovDiagonalPlusRankoneSpectrum

namespace Omega.POM

/-- Paper label: `cor:pom-maxent-markov-optimal-coupling-latent-binary-mixture`.
In the one-state optimal-coupling model, the product law and the diagonal law coincide. Hence the
unique optimal coupling can be written as a two-component latent binary mixture with weights
`A² = 1 / 4` and `θ = 3 / 4`, satisfying `A² + θ = 1`. -/
theorem paper_pom_maxent_markov_optimal_coupling_latent_binary_mixture :
    ∃ A θ : ℝ,
      0 ≤ A ∧
      0 ≤ θ ∧
      A ^ 2 + θ = 1 ∧
      ∃ Z : Bool → Unit × Unit → ℝ,
        (Z false = fun p : Unit × Unit => unitStationaryWeight p.1 * unitStationaryWeight p.2) ∧
        (Z true = fun p : Unit × Unit => if p.1 = p.2 then unitStationaryWeight p.1 else 0) ∧
        (stationaryCouplingOfKernel unitStationaryKernel =
          fun p : Unit × Unit => A ^ 2 * Z false p + θ * Z true p) := by
  refine ⟨(1 / 2 : ℝ), (3 / 4 : ℝ), by positivity, by positivity, by norm_num, ?_⟩
  refine ⟨fun b p => if b then (if p.1 = p.2 then unitStationaryWeight p.1 else 0)
      else unitStationaryWeight p.1 * unitStationaryWeight p.2, rfl, rfl, ?_⟩
  funext p
  rcases p with ⟨x, y⟩
  cases x
  cases y
  simp [stationaryCouplingOfKernel, unitStationaryKernel, unitStationaryWeight]
  norm_num

end Omega.POM
