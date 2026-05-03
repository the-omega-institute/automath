import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- A finite prime-register exponent vector over a prefixed finite index set. -/
structure xi_prime_externalization_norm_one_consistency_register (n : ℕ) where
  exponent : Fin n → ℕ

/-- The archimedean register norm `N(r) = ∏ pᵢ ^ rᵢ` for a chosen finite prime list. -/
def xi_prime_externalization_norm_one_consistency_archimedean {n : ℕ}
    (prime : Fin n → ℕ) (r : xi_prime_externalization_norm_one_consistency_register n) : ℕ :=
  ∏ i : Fin n, prime i ^ r.exponent i

/-- The symbolic local `p`-adic norm contribution attached to one finite register coordinate. -/
def xi_prime_externalization_norm_one_consistency_local_norm {n : ℕ}
    (prime : Fin n → ℕ) (r : xi_prime_externalization_norm_one_consistency_register n)
    (i : Fin n) : ℕ :=
  prime i ^ r.exponent i

/-- Product of the finite local norm contributions. -/
def xi_prime_externalization_norm_one_consistency_local_product {n : ℕ}
    (prime : Fin n → ℕ) (r : xi_prime_externalization_norm_one_consistency_register n) : ℕ :=
  ∏ i : Fin n, xi_prime_externalization_norm_one_consistency_local_norm prime r i

lemma xi_prime_externalization_norm_one_consistency_local_product_eq_archimedean {n : ℕ}
    (prime : Fin n → ℕ) (r : xi_prime_externalization_norm_one_consistency_register n) :
    xi_prime_externalization_norm_one_consistency_local_product prime r =
      xi_prime_externalization_norm_one_consistency_archimedean prime r := by
  simp [xi_prime_externalization_norm_one_consistency_local_product,
    xi_prime_externalization_norm_one_consistency_local_norm,
    xi_prime_externalization_norm_one_consistency_archimedean]

/-- The finite-support norm-one formula and its reverse unique exponent recovery. -/
def xi_prime_externalization_norm_one_consistency_statement : Prop :=
  (∀ {n : ℕ} (prime : Fin n → ℕ)
      (r : xi_prime_externalization_norm_one_consistency_register n),
      xi_prime_externalization_norm_one_consistency_archimedean prime r ≠ 0 →
        ((xi_prime_externalization_norm_one_consistency_archimedean prime r : ℚ)⁻¹ *
            (xi_prime_externalization_norm_one_consistency_local_product prime r : ℚ) = 1)) ∧
    (∀ {n : ℕ} (prime : Fin n → ℕ) (e : Fin n → ℕ) (aInf : ℕ),
      aInf = ∏ i : Fin n, prime i ^ e i →
        ∃! r : xi_prime_externalization_norm_one_consistency_register n,
          r.exponent = e ∧
            xi_prime_externalization_norm_one_consistency_archimedean prime r = aInf)

/-- Paper label: `prop:xi-prime-externalization-norm-one-consistency`. -/
theorem paper_xi_prime_externalization_norm_one_consistency :
    xi_prime_externalization_norm_one_consistency_statement := by
  constructor
  · intro n prime r harch
    rw [xi_prime_externalization_norm_one_consistency_local_product_eq_archimedean]
    exact inv_mul_cancel₀ (by
      exact_mod_cast harch :
        (xi_prime_externalization_norm_one_consistency_archimedean prime r : ℚ) ≠ 0)
  · intro n prime e aInf haInf
    refine ⟨⟨e⟩, ?_, ?_⟩
    · constructor
      · rfl
      · simpa [xi_prime_externalization_norm_one_consistency_archimedean] using haInf.symm
    · intro r hr
      cases r with
      | mk exponent =>
          cases hr.1
          rfl

end Omega.Zeta
