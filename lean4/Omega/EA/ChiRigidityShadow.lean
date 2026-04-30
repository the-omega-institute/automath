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

/-- Sign is invariant under double conjugation (outer-then-inner).
    thm:fold-groupoid-chi-rigidity -/
theorem sign_double_conj_eq_sign {α : Type*} [Fintype α] [DecidableEq α]
    (σ ρ τ : Equiv.Perm α) :
    Equiv.Perm.sign (σ * (ρ * τ * ρ⁻¹) * σ⁻¹) = Equiv.Perm.sign τ := by
  rw [sign_conj_eq_sign, sign_conj_eq_sign]

/-- Sign of the inverse of a conjugate power equals the k-th power of the sign.
    thm:fold-groupoid-chi-rigidity -/
theorem sign_conj_pow_inv_eq {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) (k : Nat) :
    Equiv.Perm.sign ((σ * τ ^ k * σ⁻¹)⁻¹) = (Equiv.Perm.sign τ) ^ k := by
  rw [Equiv.Perm.sign_inv, sign_conj_pow_eq_sign_pow]

/-- Full chi-rigidity homomorphism package: multiplicativity, inverse invariance,
    conjugation invariance (single + double), power, and ±1 dichotomy.
    thm:fold-groupoid-chi-rigidity -/
theorem paper_chi_rigidity_full_homomorphism_package
    (α : Type*) [Fintype α] [DecidableEq α] :
    (∀ σ τ : Equiv.Perm α,
       Equiv.Perm.sign (σ * τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ) ∧
    (∀ σ : Equiv.Perm α,
       Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ) ∧
    (∀ σ τ : Equiv.Perm α,
       Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ) ∧
    (∀ σ ρ τ : Equiv.Perm α,
       Equiv.Perm.sign (σ * (ρ * τ * ρ⁻¹) * σ⁻¹) = Equiv.Perm.sign τ) ∧
    (∀ σ : Equiv.Perm α, ∀ k : Nat,
       Equiv.Perm.sign (σ ^ k) = (Equiv.Perm.sign σ) ^ k) ∧
    (∀ σ : Equiv.Perm α,
       (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros σ τ; exact Equiv.Perm.sign_mul σ τ
  · exact sign_inv_eq_sign
  · exact sign_conj_eq_sign
  · exact sign_double_conj_eq_sign
  · intros σ k; exact map_pow Equiv.Perm.sign σ k
  · intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · left; rw [hs]; rfl
    · right; rw [hs]; rfl

/-- Paper-label chi-rigidity wrapper for sign invariance under block conjugation.
    thm:fold-groupoid-chi-rigidity -/
theorem paper_fold_groupoid_chi_rigidity (α : Type*) [Fintype α] [DecidableEq α] :
    (∀ σ τ : Equiv.Perm α, Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ) ∧
    (∀ σ ρ τ : Equiv.Perm α,
      Equiv.Perm.sign (σ * (ρ * τ * ρ⁻¹) * σ⁻¹) = Equiv.Perm.sign τ) :=
  ⟨sign_conj_eq_sign, sign_double_conj_eq_sign⟩

end Omega.EA
