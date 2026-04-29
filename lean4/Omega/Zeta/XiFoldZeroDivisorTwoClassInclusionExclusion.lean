import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Label-prefixed finite zero-divisor two-class package inside `ZMod m`. -/
structure xi_fold_zero_divisor_two_class_inclusion_exclusion_data where
  xi_fold_zero_divisor_two_class_inclusion_exclusion_m : ℕ
  xi_fold_zero_divisor_two_class_inclusion_exclusion_left :
    Finset (ZMod xi_fold_zero_divisor_two_class_inclusion_exclusion_m)
  xi_fold_zero_divisor_two_class_inclusion_exclusion_right :
    Finset (ZMod xi_fold_zero_divisor_two_class_inclusion_exclusion_m)
  xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set :
    Finset (ZMod xi_fold_zero_divisor_two_class_inclusion_exclusion_m)
  xi_fold_zero_divisor_two_class_inclusion_exclusion_fibonacci_gcd : ℕ
  xi_fold_zero_divisor_two_class_inclusion_exclusion_left_subset :
    xi_fold_zero_divisor_two_class_inclusion_exclusion_left ⊆
      xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set
  xi_fold_zero_divisor_two_class_inclusion_exclusion_right_subset :
    xi_fold_zero_divisor_two_class_inclusion_exclusion_right ⊆
      xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set
  xi_fold_zero_divisor_two_class_inclusion_exclusion_cover :
    xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set ⊆
      xi_fold_zero_divisor_two_class_inclusion_exclusion_left ∪
        xi_fold_zero_divisor_two_class_inclusion_exclusion_right
  xi_fold_zero_divisor_two_class_inclusion_exclusion_intersection_certificate :
    (xi_fold_zero_divisor_two_class_inclusion_exclusion_left ∩
        xi_fold_zero_divisor_two_class_inclusion_exclusion_right).card =
      xi_fold_zero_divisor_two_class_inclusion_exclusion_fibonacci_gcd

/-- The concrete inclusion-exclusion conclusion after substituting the supplied Fibonacci-gcd
intersection certificate. -/
def xi_fold_zero_divisor_two_class_inclusion_exclusion_statement
    (D : xi_fold_zero_divisor_two_class_inclusion_exclusion_data) : Prop :=
  D.xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set.card =
      D.xi_fold_zero_divisor_two_class_inclusion_exclusion_left.card +
        D.xi_fold_zero_divisor_two_class_inclusion_exclusion_right.card -
          D.xi_fold_zero_divisor_two_class_inclusion_exclusion_fibonacci_gcd ∧
    D.xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set =
      D.xi_fold_zero_divisor_two_class_inclusion_exclusion_left ∪
        D.xi_fold_zero_divisor_two_class_inclusion_exclusion_right

/-- Paper label: `thm:xi-fold-zero-divisor-two-class-inclusion-exclusion`. -/
theorem paper_xi_fold_zero_divisor_two_class_inclusion_exclusion
    (D : xi_fold_zero_divisor_two_class_inclusion_exclusion_data) :
    xi_fold_zero_divisor_two_class_inclusion_exclusion_statement D := by
  have hcover :
      D.xi_fold_zero_divisor_two_class_inclusion_exclusion_zero_set =
        D.xi_fold_zero_divisor_two_class_inclusion_exclusion_left ∪
          D.xi_fold_zero_divisor_two_class_inclusion_exclusion_right := by
    apply Finset.Subset.antisymm
    · exact D.xi_fold_zero_divisor_two_class_inclusion_exclusion_cover
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact D.xi_fold_zero_divisor_two_class_inclusion_exclusion_left_subset hx
      · exact D.xi_fold_zero_divisor_two_class_inclusion_exclusion_right_subset hx
  refine ⟨?_, ?_⟩
  · rw [hcover]
    have hcard :=
      Finset.card_union_add_card_inter
        D.xi_fold_zero_divisor_two_class_inclusion_exclusion_left
        D.xi_fold_zero_divisor_two_class_inclusion_exclusion_right
    rw [D.xi_fold_zero_divisor_two_class_inclusion_exclusion_intersection_certificate] at hcard
    omega
  · exact hcover

end Omega.Zeta
