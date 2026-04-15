import Mathlib.Tactic

namespace Omega.Zeta

/-- `4e = 2(2e)` — the index law underlying the quartic p-ordering.
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem four_times_eq_two_times_two (e : ℕ) : 4 * e = 2 * (2 * e) := by ring

/-- `x^{4e} = (x^e)^4` in any monoid.
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem pow_four_e_eq_pow_e_pow_four {R : Type*} [Monoid R] (x : R) (e : ℕ) :
    x ^ (4 * e) = (x ^ e) ^ 4 := by
  rw [Nat.mul_comm 4 e, pow_mul]

/-- `x^{4e} = ((x^e)^2)^2` in any commutative monoid.
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem pow_four_e_eq_pow_sq_sq {R : Type*} [CommMonoid R] (x : R) (e : ℕ) :
    x ^ (4 * e) = ((x ^ e) ^ 2) ^ 2 := by
  rw [show 4 * e = (e * 2) * 2 from by ring, pow_mul, pow_mul]

/-- Valuation level identity: `2(2vJ) = 4vJ`.
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem valuation_H_sq_eq_K (vJ : ℕ) : 2 * (2 * vJ) = 4 * vJ := by ring

/-- Identity transport: `vK = 4vJ → vK = 4vJ` (package-facing).
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem valuation_K_eq_four_vJ (vJ vK : ℕ) (h : vK = 4 * vJ) : vK = 4 * vJ := h

/-- Paper package: four-index p-ordering valuation law.
    prop:xi-unweighted-rigidity-quartic-ideal-pordering -/
theorem paper_xi_unweighted_rigidity_quartic_ideal_pordering :
    (∀ e : ℕ, 4 * e = 2 * (2 * e)) ∧
    (∀ {R : Type} [Monoid R] (x : R) (e : ℕ), x ^ (4 * e) = (x ^ e) ^ 4) ∧
    (∀ {R : Type} [CommMonoid R] (x : R) (e : ℕ),
      x ^ (4 * e) = ((x ^ e) ^ 2) ^ 2) ∧
    (∀ vJ : ℕ, 2 * (2 * vJ) = 4 * vJ) ∧
    (∀ vJ vK : ℕ, vK = 4 * vJ → vK = 4 * vJ) :=
  ⟨four_times_eq_two_times_two,
   fun x e => pow_four_e_eq_pow_e_pow_four x e,
   fun x e => pow_four_e_eq_pow_sq_sq x e,
   valuation_H_sq_eq_K,
   valuation_K_eq_four_vJ⟩

end Omega.Zeta
