import Mathlib.Tactic

namespace Omega.Zeta

/-- Unit seed carrier for the terminal-bit two-atom quantile collapse model. -/
abbrev xi_time_part70ab_uniform_quantile_two_atom_collapse_data := PUnit

namespace xi_time_part70ab_uniform_quantile_two_atom_collapse_data

/-- Lower terminal-bit cluster after scaling. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom : ℚ := 1 / 2

/-- Upper terminal-bit cluster after scaling. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom : ℚ := 1

/-- Critical limiting mass separating the two terminal-bit clusters. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_critical_mass : ℚ := 1 / 3

/-- Open epsilon interval around the lower scaled atom. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_left_neighborhood
    (ε y : ℚ) : Prop :=
  xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom - ε < y ∧
    y < xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom + ε

/-- Open epsilon interval around the upper scaled atom. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_right_neighborhood
    (ε y : ℚ) : Prop :=
  xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom - ε < y ∧
    y < xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom + ε

/-- Left-continuous two-atom quantile limit in the concrete seed model. -/
def xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile (α : ℚ) : ℚ :=
  if α ≤ xi_time_part70ab_uniform_quantile_two_atom_collapse_critical_mass then
    xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom
  else
    xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom

lemma xi_time_part70ab_uniform_quantile_two_atom_collapse_neighborhoods_disjoint
    {ε y : ℚ} (hε : ε ≤ 1 / 4) :
    ¬ (xi_time_part70ab_uniform_quantile_two_atom_collapse_left_neighborhood ε y ∧
      xi_time_part70ab_uniform_quantile_two_atom_collapse_right_neighborhood ε y) := by
  rintro ⟨hleft, hright⟩
  unfold xi_time_part70ab_uniform_quantile_two_atom_collapse_left_neighborhood at hleft
  unfold xi_time_part70ab_uniform_quantile_two_atom_collapse_right_neighborhood at hright
  unfold xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom at hleft
  unfold xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom at hright
  have hy_upper : y < 3 / 4 := by
    linarith [hleft.2]
  have hy_lower : 3 / 4 < y := by
    linarith [hright.1]
  linarith

/-- Concrete proposition encoding the two separated terminal clusters and their quantile split. -/
def twoAtomQuantileCollapse (_D : xi_time_part70ab_uniform_quantile_two_atom_collapse_data) :
    Prop :=
  (∀ ε y : ℚ, 0 < ε → ε ≤ 1 / 4 →
    ¬ (xi_time_part70ab_uniform_quantile_two_atom_collapse_left_neighborhood ε y ∧
      xi_time_part70ab_uniform_quantile_two_atom_collapse_right_neighborhood ε y)) ∧
  (∀ α : ℚ, 0 < α →
    α < xi_time_part70ab_uniform_quantile_two_atom_collapse_critical_mass →
      xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile α =
        xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom) ∧
  (∀ α : ℚ, xi_time_part70ab_uniform_quantile_two_atom_collapse_critical_mass < α →
    α < 1 →
      xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile α =
        xi_time_part70ab_uniform_quantile_two_atom_collapse_right_atom) ∧
  xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile
      xi_time_part70ab_uniform_quantile_two_atom_collapse_critical_mass =
    xi_time_part70ab_uniform_quantile_two_atom_collapse_left_atom

end xi_time_part70ab_uniform_quantile_two_atom_collapse_data

/-- Paper label: `thm:xi-time-part70ab-uniform-quantile-two-atom-collapse`. -/
theorem paper_xi_time_part70ab_uniform_quantile_two_atom_collapse
    (D : xi_time_part70ab_uniform_quantile_two_atom_collapse_data) :
    D.twoAtomQuantileCollapse := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε y _hεpos hε
    exact xi_time_part70ab_uniform_quantile_two_atom_collapse_data.xi_time_part70ab_uniform_quantile_two_atom_collapse_neighborhoods_disjoint hε
  · intro α _hαpos hα
    simp [xi_time_part70ab_uniform_quantile_two_atom_collapse_data.xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile,
      le_of_lt hα]
  · intro α hα _hαlt
    simp [xi_time_part70ab_uniform_quantile_two_atom_collapse_data.xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile,
      not_le.mpr hα]
  · simp [xi_time_part70ab_uniform_quantile_two_atom_collapse_data.xi_time_part70ab_uniform_quantile_two_atom_collapse_limit_quantile]

end Omega.Zeta
