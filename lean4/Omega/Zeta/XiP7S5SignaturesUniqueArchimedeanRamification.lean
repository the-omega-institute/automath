import Omega.Zeta.XiP7S5K5K10K20SplittingTypeTable

namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-s5-signatures-and-unique-archimedean-ramification`. -/
theorem paper_xi_p7_s5_signatures_and_unique_archimedean_ramification :
    xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_perm 1) 5
        xi_p7_s5_k5_k10_k20_splitting_type_table_points = [2, 1, 1, 1] ∧
      xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_two_subset_action 1) 10
        xi_p7_s5_k5_k10_k20_splitting_type_table_two_subsets =
          [2, 2, 2, 1, 1, 1, 1] ∧
      xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pair_action 1) 20
        xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pairs =
          [2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1] ∧
      (5 = 3 + 2 * 1) ∧
      (10 = 4 + 2 * 3) ∧
      (20 = 6 + 2 * 7) ∧
      (∃ a b : ℕ, a + b = 4 ∧ 2 * a = 6 ∧ b = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨3, 1, rfl, rfl, rfl⟩

end Omega.Zeta
