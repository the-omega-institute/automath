import Omega.GU.BdryZ2JumpUniqueness
import Mathlib.Tactic

namespace Omega.GU

/-- The `ℤ₂`-valued orientation parity carried by a `k`-sheet boundary uplift delta-set. -/
abbrev UpliftOrientationParity (k : ℕ) := Equiv.Perm (Fin k) →* ℤˣ

/-- The canonical uplift orientation parity is the sign character on the labeling torsor. -/
noncomputable def upliftOrientationParity (k : ℕ) : UpliftOrientationParity k :=
  signHom k

/-- Relabeling a finite delta-set only conjugates the symmetric-group action, so the orientation
parity is invariant. -/
theorem upliftOrientationParity_relabel (k : ℕ) (τ σ : Equiv.Perm (Fin k)) :
    upliftOrientationParity k (τ * σ * τ⁻¹) = upliftOrientationParity k σ := by
  have hτ : Equiv.Perm.sign τ * Equiv.Perm.sign τ = 1 := sign_sq_eq_one τ
  calc
    upliftOrientationParity k (τ * σ * τ⁻¹)
        = Equiv.Perm.sign τ * Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
          simp [upliftOrientationParity, signHom, mul_assoc]
    _ = Equiv.Perm.sign σ * (Equiv.Perm.sign τ * Equiv.Perm.sign τ) := by
      ac_rfl
    _ = Equiv.Perm.sign σ := by
      rw [hτ, mul_one]

/-- On a two-sheet uplift fiber, the nontrivial parity is the swap parity. -/
theorem upliftOrientationParity_two_swap :
    upliftOrientationParity 2 (Equiv.swap 0 1) = -1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simpa [upliftOrientationParity, signHom] using
    Equiv.Perm.sign_swap h01

/-- For three sheets, every nontrivial binary jump object agrees with the orientation parity. -/
theorem upliftOrientationParity_three_unique
    (φ : Equiv.Perm (Fin 3) →* ℤˣ) (hφ : φ ≠ 1) :
    φ = upliftOrientationParity 3 := by
  rcases paper_bdry_binary_jump_orientation_functor_uniqueness 3 (by decide) φ with hφtriv | hφsign
  · exact (hφ hφtriv).elim
  · simpa [upliftOrientationParity, signHom] using hφsign

/-- Paper-facing corollary: uplift parity is the orientation torsor, functorial under relabeling,
coincides with the unique nontrivial two-sheet parity, and is the unique nontrivial three-sheet
binary jump object.
    cor:bdry-uplift-orientation-parity -/
theorem paper_bdry_uplift_orientation_parity :
    (∀ k : ℕ, ∀ τ σ : Equiv.Perm (Fin k),
      upliftOrientationParity k (τ * σ * τ⁻¹) = upliftOrientationParity k σ) ∧
    upliftOrientationParity 2 (Equiv.swap 0 1) = -1 ∧
    (∀ φ : Equiv.Perm (Fin 3) →* ℤˣ, φ ≠ 1 → φ = upliftOrientationParity 3) := by
  refine ⟨?_, ?_⟩
  · intro k τ σ
    exact upliftOrientationParity_relabel k τ σ
  · refine ⟨upliftOrientationParity_two_swap, ?_⟩
    intro φ hφ
    exact upliftOrientationParity_three_unique φ hφ

end Omega.GU
