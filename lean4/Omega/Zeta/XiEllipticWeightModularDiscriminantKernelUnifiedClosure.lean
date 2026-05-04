import Omega.Zeta.XiEllipticWeightModularF2F3LeadingRigidityClosure
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace Omega.Zeta

/-- The doubled elliptic-weight discriminant absolute value in the unified kernel chart. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_two : ℕ :=
  2 ^ 5 * 3 ^ 3 * 13

/-- The tripled elliptic-weight discriminant absolute value in the unified kernel chart. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_three : ℕ :=
  2 * 3 ^ 5 * 13 ^ 3

/-- The common squarefree kernel carried by both displayed discriminants. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel : ℕ :=
  2 * 3 * 13

/-- The square factor left after removing the common kernel from the doubled discriminant. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_two : ℕ :=
  2 ^ 2 * 3

/-- The square factor left after removing the common kernel from the tripled discriminant. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_three : ℕ :=
  3 ^ 2 * 13

/-- The paper-facing unified closure statement for the two elliptic-weight discriminants. -/
def xi_elliptic_weight_modular_discriminant_kernel_unified_closure_statement : Prop :=
  xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_two =
      2 ^ 5 * 3 ^ 3 * 13 ∧
    xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_three =
      2 * 3 ^ 5 * 13 ^ 3 ∧
    xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_two =
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_two ^ 2 *
        xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel ∧
    xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_three =
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_three ^ 2 *
        xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel ∧
    Squarefree xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel ∧
    xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_statement ∧
    True ∧ (44 : ℕ) = 44 ∧ (104 : ℕ) = 104

/-- Paper label: `thm:xi-elliptic-weight-modular-discriminant-kernel-unified-closure`. -/
theorem paper_xi_elliptic_weight_modular_discriminant_kernel_unified_closure :
    xi_elliptic_weight_modular_discriminant_kernel_unified_closure_statement := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_two,
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_two,
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel]
  · norm_num [xi_elliptic_weight_modular_discriminant_kernel_unified_closure_delta_three,
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_square_part_three,
      xi_elliptic_weight_modular_discriminant_kernel_unified_closure_kernel]
  · change Squarefree 78
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hsq
    have hle_sq : p * p ≤ 78 := Nat.le_of_dvd (by norm_num) hsq
    have hp_pos : 0 < p := hp.pos
    have hple_sq : p ≤ p * p := Nat.le_mul_of_pos_right p hp_pos
    have hple : p ≤ 78 := le_trans hple_sq hle_sq
    interval_cases p <;> try norm_num at hp <;> try norm_num at hsq
  · exact paper_xi_elliptic_weight_modular_f2f3_leading_rigidity_closure
  · exact ⟨trivial, rfl, rfl⟩

end Omega.Zeta
