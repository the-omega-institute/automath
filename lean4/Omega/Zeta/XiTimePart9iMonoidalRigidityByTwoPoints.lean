import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The orientation character of a finite symmetric group, written additively in `ZMod 2`. -/
def xi_time_part9i_monoidal_rigidity_by_two_points_orientation
    (n : ℕ) (σ : Equiv.Perm (Fin n)) : ZMod 2 :=
  if Equiv.Perm.sign σ = 1 then 0 else 1

lemma xi_time_part9i_monoidal_rigidity_by_two_points_orientation_one (n : ℕ) :
    xi_time_part9i_monoidal_rigidity_by_two_points_orientation n 1 = 0 := by
  simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation]

lemma xi_time_part9i_monoidal_rigidity_by_two_points_orientation_mul
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    xi_time_part9i_monoidal_rigidity_by_two_points_orientation n (σ * τ) =
      xi_time_part9i_monoidal_rigidity_by_two_points_orientation n σ +
        xi_time_part9i_monoidal_rigidity_by_two_points_orientation n τ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hτ | hτ
  · simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation, hσ, hτ]
  · simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation, hσ, hτ]
  · simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation, hσ, hτ]
  · simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation, hσ, hτ]
    native_decide

lemma xi_time_part9i_monoidal_rigidity_by_two_points_orientation_swap
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    xi_time_part9i_monoidal_rigidity_by_two_points_orientation n (Equiv.swap i j) = 1 := by
  have hneg : (-1 : ℤˣ) ≠ 1 := by
    norm_num [Units.ext_iff]
  simp [xi_time_part9i_monoidal_rigidity_by_two_points_orientation,
    Equiv.Perm.sign_swap hij, hneg]

/-- A family of additive `ZMod 2` characters on the finite symmetric groups. -/
def xi_time_part9i_monoidal_rigidity_by_two_points_is_character
    (χ : ∀ n : ℕ, Equiv.Perm (Fin n) → ZMod 2) : Prop :=
  (∀ n : ℕ, χ n 1 = 0) ∧
    ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)), χ n (σ * τ) = χ n σ + χ n τ

/-- Block-sum naturality pins every transposition to the same two-point jump value. -/
def xi_time_part9i_monoidal_rigidity_by_two_points_block_sum_natural
    (χ : ∀ n : ℕ, Equiv.Perm (Fin n) → ZMod 2) : Prop :=
  ∀ (n : ℕ) (i j : Fin n), i ≠ j →
    χ n (Equiv.swap i j) = χ 2 (Equiv.swap (0 : Fin 2) (1 : Fin 2))

lemma xi_time_part9i_monoidal_rigidity_by_two_points_zmod_two_cases (c : ZMod 2) :
    c = 0 ∨ c = 1 := by
  fin_cases c <;> simp

lemma xi_time_part9i_monoidal_rigidity_by_two_points_trivial_of_zero
    (χ : ∀ n : ℕ, Equiv.Perm (Fin n) → ZMod 2)
    (hχ : xi_time_part9i_monoidal_rigidity_by_two_points_is_character χ)
    (hblock : xi_time_part9i_monoidal_rigidity_by_two_points_block_sum_natural χ)
    (hzero : χ 2 (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = 0) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), χ n σ = 0 := by
  intro n σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      exact hχ.1 n
  | swap_mul τ i j hij hτ =>
      rw [hχ.2 n (Equiv.swap i j) τ, hblock n i j hij, hzero, hτ, zero_add]

lemma xi_time_part9i_monoidal_rigidity_by_two_points_orientation_of_one
    (χ : ∀ n : ℕ, Equiv.Perm (Fin n) → ZMod 2)
    (hχ : xi_time_part9i_monoidal_rigidity_by_two_points_is_character χ)
    (hblock : xi_time_part9i_monoidal_rigidity_by_two_points_block_sum_natural χ)
    (hone : χ 2 (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = 1) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      χ n σ = xi_time_part9i_monoidal_rigidity_by_two_points_orientation n σ := by
  intro n σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      rw [hχ.1 n, xi_time_part9i_monoidal_rigidity_by_two_points_orientation_one]
  | swap_mul τ i j hij hτ =>
      rw [hχ.2 n (Equiv.swap i j) τ, hblock n i j hij, hone, hτ,
        xi_time_part9i_monoidal_rigidity_by_two_points_orientation_mul,
        xi_time_part9i_monoidal_rigidity_by_two_points_orientation_swap hij]

/-- Concrete classification of monoidal `ZMod 2` jump characters by their two-point value. -/
def xi_time_part9i_monoidal_rigidity_by_two_points_classification : Prop :=
  ∀ χ : ∀ n : ℕ, Equiv.Perm (Fin n) → ZMod 2,
    xi_time_part9i_monoidal_rigidity_by_two_points_is_character χ →
      xi_time_part9i_monoidal_rigidity_by_two_points_block_sum_natural χ →
        (∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), χ n σ = 0) ∨
          ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
            χ n σ = xi_time_part9i_monoidal_rigidity_by_two_points_orientation n σ

/-- Paper label: `thm:xi-time-part9i-monoidal-rigidity-by-two-points`. -/
theorem paper_xi_time_part9i_monoidal_rigidity_by_two_points :
    xi_time_part9i_monoidal_rigidity_by_two_points_classification := by
  intro χ hχ hblock
  rcases xi_time_part9i_monoidal_rigidity_by_two_points_zmod_two_cases
      (χ 2 (Equiv.swap (0 : Fin 2) (1 : Fin 2))) with hzero | hone
  · exact Or.inl
      (xi_time_part9i_monoidal_rigidity_by_two_points_trivial_of_zero χ hχ hblock hzero)
  · exact Or.inr
      (xi_time_part9i_monoidal_rigidity_by_two_points_orientation_of_one χ hχ hblock hone)

end Omega.Zeta
