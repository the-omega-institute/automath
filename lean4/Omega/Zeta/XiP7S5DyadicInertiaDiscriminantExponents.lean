import Omega.Zeta.XiP7S5K5K10K20SplittingTypeTable

namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-s5-dyadic-inertia-and-discriminant-exponents`. -/
theorem paper_xi_p7_s5_dyadic_inertia_and_discriminant_exponents :
    xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_perm 3) 5
        xi_p7_s5_k5_k10_k20_splitting_type_table_points = [3, 1, 1] ∧
      xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_two_subset_action 3) 10
        xi_p7_s5_k5_k10_k20_splitting_type_table_two_subsets = [3, 3, 3, 1] ∧
      xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
        (xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pair_action 3) 20
        xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pairs =
          [3, 3, 3, 3, 3, 3, 1, 1] ∧
      (10 - 4 = 6) ∧
      (20 - 8 = 12) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Omega.Zeta
