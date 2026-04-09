import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.GU

/-- Sign homomorphism on the symmetric group (used as the Z₂-torsor jump functor).
    thm:bdry-z2-jump-functor-uniqueness -/
noncomputable def signHom (k : ℕ) : Equiv.Perm (Fin k) →* ℤˣ :=
  Equiv.Perm.sign

/-- Existence of a Z₂-valued homomorphism from S_k.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem signHom_exists (k : ℕ) :
    ∃ φ : Equiv.Perm (Fin k) →* ℤˣ, φ = Equiv.Perm.sign :=
  ⟨Equiv.Perm.sign, rfl⟩

/-- The trivial Z₂-valued homomorphism.
    thm:bdry-z2-jump-functor-uniqueness -/
noncomputable def trivHom (k : ℕ) : Equiv.Perm (Fin k) →* ℤˣ := 1

/-- Sign takes values in {±1}.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem sign_range_pm_one {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-- Sign squared is the identity.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem sign_sq_eq_one {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; rfl
  · rw [h]; rfl

/-- The trivial homomorphism sends every permutation to 1.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem trivHom_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) : trivHom k σ = 1 := rfl

/-- For `k ≥ 2`, sign is a non-trivial homomorphism.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem sign_neq_triv (k : ℕ) (hk : 2 ≤ k) :
    (Equiv.Perm.sign : Equiv.Perm (Fin k) →* ℤˣ) ≠ 1 := by
  intro habs
  -- Construct the transposition ⟨0, ..⟩ ⟨1, ..⟩
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  set a : Fin k := ⟨0, h0⟩ with ha
  set b : Fin k := ⟨1, h1⟩ with hb
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    simp [ha, hb] at hval
  have hsign : Equiv.Perm.sign (Equiv.swap a b) = -1 := Equiv.Perm.sign_swap hab
  have hone : (1 : Equiv.Perm (Fin k) →* ℤˣ) (Equiv.swap a b) = 1 := rfl
  have : Equiv.Perm.sign (Equiv.swap a b) = 1 := by
    rw [habs]; exact hone
  rw [this] at hsign
  exact absurd hsign (by decide)

/-- Paper package: Z₂-valued jump functor uniqueness skeleton.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem paper_bdry_z2_jump_functor_skeleton :
    (∀ k : ℕ, ∃ φ : Equiv.Perm (Fin k) →* ℤˣ, φ = Equiv.Perm.sign) ∧
    (∀ k : ℕ, ∀ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1) ∧
    (∀ k : ℕ, ∀ σ : Equiv.Perm (Fin k),
      Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1) ∧
    (∀ k : ℕ, 2 ≤ k →
      (Equiv.Perm.sign : Equiv.Perm (Fin k) →* ℤˣ) ≠ 1) :=
  ⟨signHom_exists,
   fun _ σ => sign_range_pm_one σ,
   fun _ σ => sign_sq_eq_one σ,
   sign_neq_triv⟩

end Omega.GU
