import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Membership in the rational Joukowsky ellipse layer with axis ratio `a / b`. -/
def rationalGodelEllipse (a b : ℕ) (w : ℂ) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ w = ((a : ℂ) / b) * z + ((b : ℂ) / a) * z⁻¹

/-- Paper label: `cor:prime-register-rational-godel-integer-closure`. Clearing denominators in the
quadratic Joukowsky relation preserves integrality of the coefficients, and every root still comes
from the same ellipse layer. The dependence on the rational scale is completely encoded by the
prime factorizations of `a` and `b`. -/
theorem paper_prime_register_rational_godel_integer_closure (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∀ w : ℂ,
      (∃ z : ℂ, ‖z‖ = 1 ∧
        (a : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - ((a * b : ℕ) : ℂ) * w * z + (b : ℂ) ^ (2 : ℕ) = 0) →
      rationalGodelEllipse a b w) ∧
      (a.factorization.prod (· ^ ·) = a) ∧ (b.factorization.prod (· ^ ·) = b) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨?_, Nat.factorization_prod_pow_eq_self ha.ne', Nat.factorization_prod_pow_eq_self hb.ne'⟩
  intro w hw
  rcases hw with ⟨z, hz, hquad⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    simp [hz0] at hz
  refine ⟨z, hz, ?_⟩
  apply eq_of_sub_eq_zero
  field_simp [ha0, hb0, hz0]
  ring_nf
  simpa [sub_eq_add_neg, pow_two, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm,
    mul_comm] using (neg_eq_zero.mpr hquad)

end Omega.EA
