import Mathlib.Tactic
import Omega.POM.MomentMinreal

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete truncated moment data for
`prop:xi-truncated-moment-min-atomic-realization`. The POM minimal-realization package supplies the
Hankel-rank comparison, while the displayed nodes and weights are the finite atomic Gauss
reconstruction witness for the first `2r` moments. -/
structure xi_truncated_moment_min_atomic_realization_data where
  momentMinreal : Omega.POM.MomentMinrealData
  moments : ℕ → ℝ
  nodes : Fin momentMinreal.minimalRealizationDim → ℝ
  weights : Fin momentMinreal.minimalRealizationDim → ℝ
  gauss_reconstruction :
    ∀ n : ℕ, n < 2 * momentMinreal.recurrenceOrder →
      moments n = ∑ j, weights j * nodes j ^ n

/-- The truncated moment profile has a finite atomic realization whose support size is bounded by
the Hankel-rank parameter, and that realization matches the first `2r` moments. -/
def xi_truncated_moment_min_atomic_realization_statement
    (D : xi_truncated_moment_min_atomic_realization_data) : Prop :=
  ∃ r : ℕ, ∃ nodes : Fin r → ℝ, ∃ weights : Fin r → ℝ,
    r ≤ D.momentMinreal.hankelRank ∧
      ∀ n : ℕ, n < 2 * D.momentMinreal.recurrenceOrder →
        D.moments n = ∑ j, weights j * nodes j ^ n

/-- Paper label: `prop:xi-truncated-moment-min-atomic-realization`. -/
theorem paper_xi_truncated_moment_min_atomic_realization
    (D : xi_truncated_moment_min_atomic_realization_data) :
    xi_truncated_moment_min_atomic_realization_statement D := by
  rcases Omega.POM.paper_pom_moment_minreal D.momentMinreal with ⟨hrank, hdim⟩
  refine ⟨D.momentMinreal.minimalRealizationDim, D.nodes, D.weights, ?_, ?_⟩
  · rw [hdim, ← hrank]
  · exact D.gauss_reconstruction

end Omega.Zeta
