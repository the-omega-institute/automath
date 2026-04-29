import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedCollisionPressureSingularRing

namespace Omega.DerivedConsequences

noncomputable section

/-- The geometric majorant induced by a Cauchy estimate on the `R`-circle. -/
def derived_collision_cumulants_radius_cauchy_rootunity_geometric_majorant
    (M R θ : ℝ) (n : ℕ) : ℝ :=
  M * (|θ| / R) ^ n

/-- The radius of the `p`-th root-of-unity sampling point `2π i / p`. -/
def derived_collision_cumulants_radius_cauchy_rootunity_rootunity_radius (p : ℕ) : ℝ :=
  2 * Real.pi / p

/-- Paper label: `cor:derived-collision-cumulants-radius-cauchy-rootunity`. The singular-ring
package records the exact nearest branch radius, every Cauchy geometric majorant with `|θ| < R`
is summable, and every root-of-unity sample with `p ≥ 3` lies strictly inside the analytic
radius. -/
theorem paper_derived_collision_cumulants_radius_cauchy_rootunity :
    derived_collision_pressure_singular_ring_nearest_radius = 2.76230289346087 ∧
      (∀ {M R θ : ℝ}, 0 ≤ M → 0 < R →
        |θ| < R →
        Summable
          (derived_collision_cumulants_radius_cauchy_rootunity_geometric_majorant M R θ)) ∧
      (∀ p : ℕ, 3 ≤ p →
        derived_collision_cumulants_radius_cauchy_rootunity_rootunity_radius p <
          derived_collision_pressure_singular_ring_nearest_radius) := by
  rcases paper_derived_collision_pressure_singular_ring with ⟨_, _, _, _, _, _, _, _, hrad⟩
  refine ⟨hrad, ?_, ?_⟩
  · intro M R θ hM hR0 htheta
    have hratio_nonneg : 0 ≤ |θ| / R := by positivity
    have hratio_lt_one : |θ| / R < 1 := by
      rw [div_lt_iff₀ hR0]
      nlinarith
    simpa [derived_collision_cumulants_radius_cauchy_rootunity_geometric_majorant] using
      (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left M
  · intro p hp
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hp)
    have hpR3 : (3 : ℝ) ≤ p := by
      exact_mod_cast hp
    have hdiv :
        derived_collision_cumulants_radius_cauchy_rootunity_rootunity_radius p ≤
          2 * Real.pi / 3 := by
      unfold derived_collision_cumulants_radius_cauchy_rootunity_rootunity_radius
      rw [div_le_div_iff₀ hpR (by norm_num : (0 : ℝ) < 3)]
      nlinarith [Real.pi_pos, hpR3]
    have hconst : 2 * Real.pi / 3 < derived_collision_pressure_singular_ring_nearest_radius := by
      rw [hrad]
      nlinarith [Real.pi_lt_four]
    exact lt_of_le_of_lt hdiv hconst

end

end Omega.DerivedConsequences
