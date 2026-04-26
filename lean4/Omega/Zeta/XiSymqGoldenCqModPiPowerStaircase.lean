import Mathlib.Tactic

namespace Omega.Zeta

/-- The `π^r` diagonal entry after reduction modulo `π^t`: exponents below `t` survive,
while exponents at least `t` vanish. -/
def xi_symq_golden_cq_mod_pi_power_staircase_diagonal_entry (t r : Nat) : Nat :=
  if r < t then 1 else 0

/-- The number of nonzero diagonal generators in the reduced Smith staircase. -/
def xi_symq_golden_cq_mod_pi_power_staircase_image_minimal_generator_rank
    (q t : Nat) : Nat :=
  min t (q + 1)

/-- Concrete quotient-level staircase statement for the Smith exponents `0, ..., q`. -/
def xi_symq_golden_cq_mod_pi_power_staircase_statement (q t : Nat) : Prop :=
  1 ≤ t ∧
  (∀ r : Fin (q + 1), t ≤ r.val →
    xi_symq_golden_cq_mod_pi_power_staircase_diagonal_entry t r.val = 0) ∧
  (∀ r : Fin (q + 1), r.val < t →
    xi_symq_golden_cq_mod_pi_power_staircase_diagonal_entry t r.val = 1) ∧
  xi_symq_golden_cq_mod_pi_power_staircase_image_minimal_generator_rank q t = t

/-- Paper label: `cor:xi-symq-golden-cq-mod-pi-power-staircase`. -/
theorem paper_xi_symq_golden_cq_mod_pi_power_staircase (q t : Nat)
    (ht : 1 <= t) (htq : t <= q + 1) :
    xi_symq_golden_cq_mod_pi_power_staircase_statement q t := by
  refine ⟨ht, ?_, ?_, ?_⟩
  · intro r hr
    simp [xi_symq_golden_cq_mod_pi_power_staircase_diagonal_entry, Nat.not_lt_of_ge hr]
  · intro r hr
    simp [xi_symq_golden_cq_mod_pi_power_staircase_diagonal_entry, hr]
  · simp [xi_symq_golden_cq_mod_pi_power_staircase_image_minimal_generator_rank,
      Nat.min_eq_left htq]

end Omega.Zeta
