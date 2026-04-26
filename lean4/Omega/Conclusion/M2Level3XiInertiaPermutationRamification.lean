import Mathlib.Tactic

namespace Omega.Conclusion

/-- Fixed projective lines in the `+1` eigenspace of the bielliptic involution on `J(C)[3]`. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_v_plus_projective_fixed : ℕ := 4

/-- Fixed projective lines in the `-1` eigenspace of the bielliptic involution on `J(C)[3]`. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_v_minus_projective_fixed : ℕ := 4

/-- Total number of projective lines in the audited `m = 2`, level-`3` model. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_projective_total : ℕ := 40

/-- Projective lines fixed by the involution. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_projective_fixed : ℕ :=
  conclusion_m2_level3_xi_inertia_permutation_ramification_v_plus_projective_fixed +
    conclusion_m2_level3_xi_inertia_permutation_ramification_v_minus_projective_fixed

/-- Residual projective-line orbits are `2`-cycles. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_projective_two_cycles : ℕ :=
  (conclusion_m2_level3_xi_inertia_permutation_ramification_projective_total -
      conclusion_m2_level3_xi_inertia_permutation_ramification_projective_fixed) /
    2

/-- Total number of Lagrangian planes in the audited model. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_total : ℕ := 40

/-- Fixed Lagrangians are direct sums `ℓ₊ ⊕ ℓ₋` of fixed lines in the two eigenspaces. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_fixed : ℕ :=
  conclusion_m2_level3_xi_inertia_permutation_ramification_v_plus_projective_fixed *
    conclusion_m2_level3_xi_inertia_permutation_ramification_v_minus_projective_fixed

/-- Residual Lagrangian orbits are `2`-cycles. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_two_cycles : ℕ :=
  (conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_total -
      conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_fixed) /
    2

/-- Total number of incident line-plane flags in the audited model. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_flag_total : ℕ := 160

/-- Each fixed Lagrangian contributes its two eigenspace lines as fixed flags. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_flag_fixed : ℕ :=
  conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_fixed * 2

/-- Residual flag orbits are `2`-cycles. -/
def conclusion_m2_level3_xi_inertia_permutation_ramification_flag_two_cycles : ℕ :=
  (conclusion_m2_level3_xi_inertia_permutation_ramification_flag_total -
      conclusion_m2_level3_xi_inertia_permutation_ramification_flag_fixed) /
    2

/-- Paper label: `thm:conclusion-m2-level3-xi-inertia-permutation-ramification`. -/
theorem paper_conclusion_m2_level3_xi_inertia_permutation_ramification :
    conclusion_m2_level3_xi_inertia_permutation_ramification_projective_fixed = 8 ∧
      conclusion_m2_level3_xi_inertia_permutation_ramification_projective_two_cycles = 16 ∧
      conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_fixed = 16 ∧
      conclusion_m2_level3_xi_inertia_permutation_ramification_lagrangian_two_cycles = 12 ∧
      conclusion_m2_level3_xi_inertia_permutation_ramification_flag_fixed = 32 ∧
      conclusion_m2_level3_xi_inertia_permutation_ramification_flag_two_cycles = 64 := by
  native_decide

end Omega.Conclusion
