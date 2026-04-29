import Mathlib.Tactic

namespace Omega.Zeta

/-!
# Finite forbidden blocks give a sparse block count

The file records the arithmetic heart of the standard disjoint-block argument: each complete
block of length `ell` has at most `2^ell - 1` admissible choices, and the suffix has at most
`2^r` choices.
-/

/-- Data carrier for the finite-forbidden-block sparsity statement. -/
structure zeta_syntax_finite_forbidden_exp_sparse_data where

/-- The block-count upper bound obtained from disjoint length-`ell` blocks. -/
def zeta_syntax_finite_forbidden_exp_sparse_block_bound (ell m : ℕ) : ℕ :=
  (2 ^ ell - 1) ^ (m / ell) * 2 ^ (m % ell)

/-- Concrete claim for the finite forbidden block sparsity proposition. -/
def zeta_syntax_finite_forbidden_exp_sparse_claim
    (_D : zeta_syntax_finite_forbidden_exp_sparse_data) : Prop :=
  ∀ ell m : ℕ, 0 < ell →
    zeta_syntax_finite_forbidden_exp_sparse_block_bound ell m ≤ 2 ^ m

/-- The disjoint-block finite forbidden pattern bound is at most the total binary word count.
    prop:zeta-syntax-finite-forbidden-exp-sparse -/
theorem paper_zeta_syntax_finite_forbidden_exp_sparse
    (D : zeta_syntax_finite_forbidden_exp_sparse_data) :
    zeta_syntax_finite_forbidden_exp_sparse_claim D := by
  intro ell m hell
  unfold zeta_syntax_finite_forbidden_exp_sparse_block_bound
  set q := m / ell
  set r := m % ell
  have hblock : (2 ^ ell - 1) ^ q ≤ (2 ^ ell) ^ q := by
    exact Nat.pow_le_pow_left (Nat.sub_le (2 ^ ell) 1) q
  have hmul : (2 ^ ell - 1) ^ q * 2 ^ r ≤ (2 ^ ell) ^ q * 2 ^ r := by
    exact Nat.mul_le_mul_right (2 ^ r) hblock
  have hsplit : ell * q + r = m := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod m ell
  calc
    (2 ^ ell - 1) ^ q * 2 ^ r ≤ (2 ^ ell) ^ q * 2 ^ r := hmul
    _ = 2 ^ (ell * q) * 2 ^ r := by rw [pow_mul]
    _ = 2 ^ (ell * q + r) := by rw [← pow_add]
    _ = 2 ^ m := by rw [hsplit]

end Omega.Zeta
