import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9n1a-prym-c6h-jz2-polarized-isogeny-degree`. -/
theorem paper_xi_time_part9n1a_prym_c6h_jz2_polarized_isogeny_degree
    (deg_f deg_lambda_A deg_lambda_B : Nat)
    (hA : deg_lambda_A = 3 ^ 8)
    (hB : deg_lambda_B = 1)
    (hcompat : deg_lambda_A = deg_f ^ 2 * deg_lambda_B) :
    deg_f = 3 ^ 4 := by
  have hsq : deg_f ^ 2 = (3 ^ 4) ^ 2 := by
    rw [hA, hB] at hcompat
    norm_num at hcompat ⊢
    exact hcompat.symm
  exact Nat.pow_left_injective (by norm_num : (2 : Nat) ≠ 0) hsq

end Omega.Zeta
