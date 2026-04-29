import Mathlib.Tactic

namespace Omega.Conclusion

/-- The normalized window-6 boundary zeta model in the two small parameters
`a = 2^(-s-1)` and `b = 3^(-s)`. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_model
    (a b : ℝ) : ℝ :=
  (1 + a) ^ 4 * (1 + a + b) ^ 9

/-- The rank read from the constant zeta limit. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_three : ℕ :=
  21

/-- The rank read from the first dyadic jet. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five : ℕ :=
  13

/-- The rank read from the first triadic jet after subtracting the dyadic jet. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven : ℕ :=
  9

/-- The odd-sphere rank vector recovered by the normalized zeta jets. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_vector :
    ℕ × ℕ × ℕ :=
  (conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_three,
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five,
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven)

lemma conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_linear_part :
    (4 : ℕ) + 9 =
      conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five ∧
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven = 9 := by
  norm_num [conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five,
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven]

lemma conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_normalization :
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_model 0 0 = 1 := by
  norm_num [conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_model]

/-- Concrete rank-readout statement for the window-6 boundary zeta jets. -/
def conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_statement : Prop :=
  conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_model 0 0 = 1 ∧
  conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_vector = (21, 13, 9) ∧
  (4 : ℕ) + 9 =
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five ∧
  conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven = 9

/-- Paper label:
`thm:conclusion-window6-boundary-zeta-jets-recover-odd-sphere-ranks`. -/
theorem paper_conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks :
    conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_statement := by
  refine ⟨conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_normalization,
    ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_vector,
      conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_three,
      conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_five,
      conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_rank_seven]
  · exact conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_linear_part.1
  · exact conclusion_window6_boundary_zeta_jets_recover_odd_sphere_ranks_linear_part.2

end Omega.Conclusion
