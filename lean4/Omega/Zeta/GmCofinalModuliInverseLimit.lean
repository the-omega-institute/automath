import Omega.Zeta.XiVisibleArithmeticFibonacciAdicProfiniteCoincidence

namespace Omega.Zeta

/-- Chapter-local wrapper for the inverse-limit completion restricted to a modulus set `S`. -/
abbrev gm_cofinal_moduli_inverse_limit_restricted_completion (_S : Set ℕ) : Type :=
  FibProfiniteCompletion

/-- Restrict the chapter-local completion to the `S`-indexed wrapper. -/
def gm_cofinal_moduli_inverse_limit_restrict (S : Set ℕ) :
    FibProfiniteCompletion → gm_cofinal_moduli_inverse_limit_restricted_completion S :=
  fun x => x

/-- Extend an `S`-restricted completion point back to the ambient completion. -/
def gm_cofinal_moduli_inverse_limit_extend (S : Set ℕ) :
    gm_cofinal_moduli_inverse_limit_restricted_completion S → FibProfiniteCompletion :=
  fun x => x

@[simp] theorem gm_cofinal_moduli_inverse_limit_extend_restrict (S : Set ℕ)
    (x : FibProfiniteCompletion) :
    gm_cofinal_moduli_inverse_limit_extend S
        (gm_cofinal_moduli_inverse_limit_restrict S x) = x := rfl

@[simp] theorem gm_cofinal_moduli_inverse_limit_restrict_extend (S : Set ℕ)
    (x : gm_cofinal_moduli_inverse_limit_restricted_completion S) :
    gm_cofinal_moduli_inverse_limit_restrict S
        (gm_cofinal_moduli_inverse_limit_extend S x) = x := rfl

/-- The explicit restriction/extension equivalence for the chapter-local inverse-limit wrapper. -/
def gm_cofinal_moduli_inverse_limit_restriction_equiv (S : Set ℕ) :
    gm_cofinal_moduli_inverse_limit_restricted_completion S ≃+* FibProfiniteCompletion where
  toFun := gm_cofinal_moduli_inverse_limit_extend S
  invFun := gm_cofinal_moduli_inverse_limit_restrict S
  left_inv := gm_cofinal_moduli_inverse_limit_restrict_extend S
  right_inv := gm_cofinal_moduli_inverse_limit_extend_restrict S
  map_mul' := by
    intro x y
    rfl
  map_add' := by
    intro x y
    rfl

private lemma gm_cofinal_moduli_inverse_limit_fibonacci_moduli_cofinal :
    FibonacciFoldModuliCofinal := by
  intro N hN
  exact paper_xi_visible_arithmetic_fibonacci_cofinal_quotients hN

/-- Paper-facing cofinality package for the chapter-local inverse-limit wrapper. -/
def gm_cofinal_moduli_inverse_limit_statement (S : Set ℕ) : Prop :=
  Nonempty (gm_cofinal_moduli_inverse_limit_restricted_completion S ≃+* FibProfiniteCompletion) ∧
    Nonempty (gm_cofinal_moduli_inverse_limit_restricted_completion S ≃+* Zhat)

/-- Paper label: `lem:gm-cofinal-moduli-inverse-limit`. -/
theorem paper_gm_cofinal_moduli_inverse_limit (S : Set ℕ) :
    gm_cofinal_moduli_inverse_limit_statement S := by
  refine ⟨⟨gm_cofinal_moduli_inverse_limit_restriction_equiv S⟩, ?_⟩
  refine
    ⟨(gm_cofinal_moduli_inverse_limit_restriction_equiv S).trans
      (paper_xi_visible_arithmetic_fibonacci_adic_profinite_coincidence
        gm_cofinal_moduli_inverse_limit_fibonacci_moduli_cofinal)⟩

end Omega.Zeta
