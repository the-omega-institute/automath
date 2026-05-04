import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete prime-power predicate used by the visible arithmetic splitting wrapper. -/
def xi_visible_arithmetic_omega_controlled_splitting_primePower (N : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ N = p ^ k

/-- Finite CRT/idempotent-count data for a visible arithmetic quotient. -/
structure xi_visible_arithmetic_omega_controlled_splitting_data where
  N : ℕ
  omega : ℕ
  idempotents : Finset ℕ
  idempotents_card : idempotents.card = 2 ^ omega
  prime_power_iff :
    xi_visible_arithmetic_omega_controlled_splitting_primePower N ↔ omega = 1

namespace xi_visible_arithmetic_omega_controlled_splitting_data

/-- The idempotent set has cardinality `2^omega`. -/
def idempotent_count (D : xi_visible_arithmetic_omega_controlled_splitting_data) : Prop :=
  D.idempotents.card = 2 ^ D.omega

/-- A nontrivial product split is equivalent to at least two visible prime-power factors. -/
def nontrivial_product_iff
    (D : xi_visible_arithmetic_omega_controlled_splitting_data) : Prop :=
  2 ≤ D.omega ↔ 4 ≤ D.idempotents.card

/-- Indecomposability is equivalent to the modulus being a prime power. -/
def indecomposable_iff_prime_power
    (D : xi_visible_arithmetic_omega_controlled_splitting_data) : Prop :=
  D.omega = 1 ↔ xi_visible_arithmetic_omega_controlled_splitting_primePower D.N

/-- In the prime case there are exactly two idempotents, hence no nontrivial CRT split. -/
def field_case (D : xi_visible_arithmetic_omega_controlled_splitting_data) : Prop :=
  Nat.Prime D.N → D.omega = 1 ∧ D.idempotents.card = 2

private lemma xi_visible_arithmetic_omega_controlled_splitting_two_le_omega_iff
    (omega : ℕ) : 2 ≤ omega ↔ 4 ≤ 2 ^ omega := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact (pow_le_pow_iff_right₀ (a := (2 : ℕ)) (by norm_num) (n := 2) (m := omega)).symm

private lemma xi_visible_arithmetic_omega_controlled_splitting_prime_is_primePower
    {N : ℕ} (hN : Nat.Prime N) :
    xi_visible_arithmetic_omega_controlled_splitting_primePower N := by
  exact ⟨N, 1, hN, by omega, by simp⟩

/-- Paper label: `thm:xi-visible-arithmetic-omega-controlled-splitting`. -/
theorem paper_xi_visible_arithmetic_omega_controlled_splitting
    (D : xi_visible_arithmetic_omega_controlled_splitting_data) :
    D.idempotent_count ∧ D.nontrivial_product_iff ∧
      D.indecomposable_iff_prime_power ∧ D.field_case := by
  refine ⟨D.idempotents_card, ?_, ?_, ?_⟩
  · rw [nontrivial_product_iff, D.idempotents_card]
    exact xi_visible_arithmetic_omega_controlled_splitting_two_le_omega_iff D.omega
  · rw [indecomposable_iff_prime_power]
    exact D.prime_power_iff.symm
  · intro hprime
    have homega : D.omega = 1 :=
      D.prime_power_iff.mp
        (xi_visible_arithmetic_omega_controlled_splitting_prime_is_primePower hprime)
    constructor
    · exact homega
    · rw [D.idempotents_card, homega]
      norm_num

end xi_visible_arithmetic_omega_controlled_splitting_data

end Omega.Zeta
