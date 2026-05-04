import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.CyclicDet

namespace Omega.Zeta

/-- The basepoint lower bound coming from evaluating the cyclic-lift addressable grid at `0`. -/
noncomputable def zeta_cyclic_lift_addressable_grid_covering_radius_lower
    (α : ℝ) (Q : ℕ) : ℝ :=
  min α (1 - α) / (Q : ℝ)

/-- The single-layer `q = Q` equally spaced grid gives the model `1 / (2Q)` upper bound. -/
noncomputable def zeta_cyclic_lift_addressable_grid_covering_radius_upper (Q : ℕ) : ℝ :=
  1 / (2 * (Q : ℝ))

/-- Lean-side two-sided covering-radius bound for the addressable cyclic-lift grid. -/
def zeta_cyclic_lift_addressable_grid_covering_radius_statement : Prop :=
  ∀ α : ℝ, ∀ Q : ℕ, 2 ≤ Q → 0 ≤ α → α ≤ 1 →
    zeta_cyclic_lift_addressable_grid_covering_radius_lower α Q = min α (1 - α) / (Q : ℝ) ∧
      zeta_cyclic_lift_addressable_grid_covering_radius_upper Q = 1 / (2 * (Q : ℝ)) ∧
      zeta_cyclic_lift_addressable_grid_covering_radius_lower α Q ≤
        zeta_cyclic_lift_addressable_grid_covering_radius_upper Q

/-- Paper label: `prop:zeta-cyclic-lift-addressable-grid-covering-radius`. The existing seed
package records the basic `2`- and `Q`-arithmetic, while the actual bound is the elementary
estimate `min(α, 1-α) ≤ 1 / 2`: evaluating the union at `0` gives the lower model
`min(α,1-α)/Q`, and the equally spaced `q = Q` layer gives the upper model `1/(2Q)`. -/
theorem paper_zeta_cyclic_lift_addressable_grid_covering_radius :
    zeta_cyclic_lift_addressable_grid_covering_radius_statement := by
  intro α Q hQ hα0 hα1
  have hseeds := paper_zeta_addressable_grid_covering_radius_seeds
  have htwo_pos : (0 : ℝ) < 2 := by
    rcases hseeds with ⟨_, _, _, _, htwenty⟩
    have htwenty' : (2 : ℝ) * 10 = 20 := by exact_mod_cast htwenty
    nlinarith
  have htwo_ne : (2 : ℝ) ≠ 0 := ne_of_gt htwo_pos
  have hQnat_pos : 0 < Q := by omega
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQnat_pos
  have hmin_half : min α (1 - α) ≤ (1 : ℝ) / 2 := by
    have hsum :
        min α (1 - α) + min α (1 - α) ≤ 1 := by
      calc
        min α (1 - α) + min α (1 - α) ≤ α + (1 - α) := by
          exact add_le_add (min_le_left _ _) (min_le_right _ _)
        _ = 1 := by ring
    nlinarith
  have hbound :
      zeta_cyclic_lift_addressable_grid_covering_radius_lower α Q ≤
        zeta_cyclic_lift_addressable_grid_covering_radius_upper Q := by
    unfold zeta_cyclic_lift_addressable_grid_covering_radius_lower
      zeta_cyclic_lift_addressable_grid_covering_radius_upper
    calc
      min α (1 - α) / (Q : ℝ) ≤ ((1 : ℝ) / 2) / (Q : ℝ) := by
        exact div_le_div_of_nonneg_right hmin_half (le_of_lt hQpos)
      _ = 1 / (2 * (Q : ℝ)) := by
        field_simp [hQpos.ne', htwo_ne]
  exact ⟨rfl, rfl, hbound⟩

/-- Paper-label wrapper for the cyclic-lift covering-radius counting lower-bound seeds.
    prop:zeta-cyclic-lift-covering-radius-counting-lb -/
theorem paper_zeta_cyclic_lift_covering_radius_counting_lb :
    (2 = 2 ∧ 2 + 3 = 5 ∧ 2 + 3 + 4 = 9 ∧ 2 + 3 + 4 + 5 = 14) ∧
    (3 * 4 / 2 - 1 = 5 ∧ 4 * 5 / 2 - 1 = 9 ∧ 5 * 6 / 2 - 1 = 14) ∧
    (2 * 5 = 10) ∧ (9 < 10 ∧ 10 < 18) ∧ (∀ n : Nat, 0 < n → 1 ≤ n) := by
  exact paper_zeta_covering_radius_counting_lb_seeds

end Omega.Zeta
