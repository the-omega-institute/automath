import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.EA

/-- Permutation sign is invariant under conjugation.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_conj_eq_sign {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) :
    Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs]
    simp
  · rw [hs]
    norm_num

/-- Conjugate permutations have the same sign.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_eq_of_conj {α : Type*} [Fintype α] [DecidableEq α]
    (τ τ' : Equiv.Perm α)
    (h : ∃ σ : Equiv.Perm α, τ' = σ * τ * σ⁻¹) :
    Equiv.Perm.sign τ' = Equiv.Perm.sign τ := by
  rcases h with ⟨σ, rfl⟩
  simpa using sign_conj_eq_sign σ τ

/-- Square of a permutation sign is 1.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_square_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs]; norm_num
  · rw [hs]; norm_num

/-- Sign of an inverse permutation equals sign of the permutation.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_inv_eq_sign {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ := by
  rw [Equiv.Perm.sign_inv]

/-- Sign of conjugate power equals k-th power of the sign.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_conj_pow_eq_sign_pow {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) (k : Nat) :
    Equiv.Perm.sign (σ * τ ^ k * σ⁻¹) = (Equiv.Perm.sign τ) ^ k := by
  rw [sign_conj_eq_sign σ (τ ^ k), map_pow]

/-- Extended chi rigidity package.
    thm:fold-groupoid-chi-rigidity -/
theorem paper_chi_rigidity_extended_package (α : Type*) [Fintype α] [DecidableEq α] :
    (∀ σ τ : Equiv.Perm α,
      Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ) ∧
    (∀ σ : Equiv.Perm α,
      Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1) ∧
    (∀ σ : Equiv.Perm α,
      Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ) ∧
    (∀ σ τ : Equiv.Perm α, ∀ k : Nat,
      Equiv.Perm.sign (σ * τ ^ k * σ⁻¹) = (Equiv.Perm.sign τ) ^ k) :=
  ⟨sign_conj_eq_sign,
   sign_square_eq_one,
   sign_inv_eq_sign,
   sign_conj_pow_eq_sign_pow⟩

end Omega.EA
