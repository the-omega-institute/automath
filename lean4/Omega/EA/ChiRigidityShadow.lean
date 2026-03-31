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

end Omega.EA
