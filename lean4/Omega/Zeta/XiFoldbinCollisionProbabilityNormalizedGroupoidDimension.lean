import Mathlib.Tactic
import Omega.EA.Wedderburn
import Omega.Folding.CollisionZeta

namespace Omega.Zeta

open scoped BigOperators

/-- The normalized collision probability is the normalized Wedderburn dimension: both numerators
are the same second moment `Σ d(w)^2`, once counted as collision pairs and once as the sum of
matrix-block dimensions. -/
def xi_foldbin_collision_probability_normalized_groupoid_dimension_statement : Prop :=
  ∀ m : ℕ,
    ((Finset.univ.filter
        (fun p : Omega.Word m × Omega.Word m => Omega.Fold p.1 = Omega.Fold p.2)).card : ℚ) /
        (4 ^ m : ℚ) =
      ((∑ x : Omega.X m, (Omega.X.fiberMultiplicity x) ^ 2 : ℕ) : ℚ) / (4 ^ m : ℚ)

theorem paper_xi_foldbin_collision_probability_normalized_groupoid_dimension :
    xi_foldbin_collision_probability_normalized_groupoid_dimension_statement := by
  intro m
  rw [← Omega.momentSum_two_eq_collision m, Omega.EA.wedderburn_total_dim_eq_S2 m]

end Omega.Zeta
