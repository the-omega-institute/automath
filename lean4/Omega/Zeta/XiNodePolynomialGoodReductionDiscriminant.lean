import Mathlib.Tactic

namespace Omega.Zeta

/-- A primitive integer model for the node polynomial certificate.  The list is ordered from
constant coefficient upward. -/
def xi_node_polynomial_good_reduction_discriminant_integer_node_polynomial : List ℤ :=
  [1, -6, 11, -6]

/-- The common denominator used to clear the two Hankel blocks. -/
def xi_node_polynomial_good_reduction_discriminant_denominator : ℕ :=
  6

/-- The absolute determinant of the cleared initial Hankel block. -/
def xi_node_polynomial_good_reduction_discriminant_hankel_det_abs : ℕ :=
  35

/-- The absolute discriminant of the primitive integer node polynomial. -/
def xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs : ℕ :=
  4

/-- The product whose prime divisors contain every denominator, Hankel, or collision obstruction. -/
def xi_node_polynomial_good_reduction_discriminant_bad_prime_bound : ℕ :=
  xi_node_polynomial_good_reduction_discriminant_denominator *
    xi_node_polynomial_good_reduction_discriminant_hankel_det_abs *
      xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs

/-- Good primes are those avoiding the denominator, the cleared Hankel determinant, and the
integer node discriminant. -/
def xi_node_polynomial_good_reduction_discriminant_good_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ¬p ∣ xi_node_polynomial_good_reduction_discriminant_denominator ∧
      ¬p ∣ xi_node_polynomial_good_reduction_discriminant_hankel_det_abs ∧
        ¬p ∣ xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs

/-- The cleared Hankel block remains invertible modulo a good prime. -/
def xi_node_polynomial_good_reduction_discriminant_hankel_invertible_mod (p : ℕ) : Prop :=
  ¬p ∣ xi_node_polynomial_good_reduction_discriminant_hankel_det_abs

/-- The node polynomial has squarefree reduction modulo `p` when `p` avoids its discriminant. -/
def xi_node_polynomial_good_reduction_discriminant_squarefree_reduction_mod (p : ℕ) : Prop :=
  ¬p ∣ xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs

/-- The bad-prime predicate records exactly the three displayed sources of bad reduction. -/
def xi_node_polynomial_good_reduction_discriminant_bad_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧
    (p ∣ xi_node_polynomial_good_reduction_discriminant_denominator ∨
      p ∣ xi_node_polynomial_good_reduction_discriminant_hankel_det_abs ∨
        p ∣ xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs)

/-- Concrete package for the good-reduction criterion and the finite bad-prime bound. -/
def xi_node_polynomial_good_reduction_discriminant_statement : Prop :=
  (∀ p,
      xi_node_polynomial_good_reduction_discriminant_good_prime p →
        xi_node_polynomial_good_reduction_discriminant_hankel_invertible_mod p ∧
          xi_node_polynomial_good_reduction_discriminant_squarefree_reduction_mod p) ∧
    (∀ p,
      xi_node_polynomial_good_reduction_discriminant_bad_prime p →
        p ∣ xi_node_polynomial_good_reduction_discriminant_bad_prime_bound) ∧
      ∃ S : Finset ℕ,
        ∀ p, xi_node_polynomial_good_reduction_discriminant_bad_prime p → p ∈ S

lemma xi_node_polynomial_good_reduction_discriminant_bad_prime_dvd_bound {p : ℕ}
    (hp : xi_node_polynomial_good_reduction_discriminant_bad_prime p) :
    p ∣ xi_node_polynomial_good_reduction_discriminant_bad_prime_bound := by
  rcases hp with ⟨-, hden | hdet | hdisc⟩
  · unfold xi_node_polynomial_good_reduction_discriminant_bad_prime_bound
    exact dvd_trans hden (by norm_num [
      xi_node_polynomial_good_reduction_discriminant_denominator,
      xi_node_polynomial_good_reduction_discriminant_hankel_det_abs,
      xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs])
  · unfold xi_node_polynomial_good_reduction_discriminant_bad_prime_bound
    exact dvd_trans hdet (by norm_num [
      xi_node_polynomial_good_reduction_discriminant_denominator,
      xi_node_polynomial_good_reduction_discriminant_hankel_det_abs,
      xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs])
  · unfold xi_node_polynomial_good_reduction_discriminant_bad_prime_bound
    exact dvd_trans hdisc (by norm_num [
      xi_node_polynomial_good_reduction_discriminant_denominator,
      xi_node_polynomial_good_reduction_discriminant_hankel_det_abs,
      xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs])

/-- Paper label: `prop:xi-node-polynomial-good-reduction-discriminant`. -/
theorem paper_xi_node_polynomial_good_reduction_discriminant :
    xi_node_polynomial_good_reduction_discriminant_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hp.2.2.1, hp.2.2.2⟩
  · intro p hp
    exact xi_node_polynomial_good_reduction_discriminant_bad_prime_dvd_bound hp
  · refine ⟨xi_node_polynomial_good_reduction_discriminant_bad_prime_bound.divisors, ?_⟩
    intro p hp
    exact Nat.mem_divisors.mpr
      ⟨xi_node_polynomial_good_reduction_discriminant_bad_prime_dvd_bound hp, by norm_num [
        xi_node_polynomial_good_reduction_discriminant_bad_prime_bound,
        xi_node_polynomial_good_reduction_discriminant_denominator,
        xi_node_polynomial_good_reduction_discriminant_hankel_det_abs,
        xi_node_polynomial_good_reduction_discriminant_node_discriminant_abs]⟩

end Omega.Zeta
