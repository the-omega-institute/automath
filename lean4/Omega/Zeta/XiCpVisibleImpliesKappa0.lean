import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The direct-sum visible block Toeplitz quadratic form. -/
def xi_cp_visible_implies_kappa0_block_quadratic
    (m N : ℕ) (c : Fin (m + 1) → ℝ) (x : Fin (m + 1) → Fin (N + 1) → ℝ) : ℝ :=
  ∑ χ : Fin (m + 1), c χ * ∑ i : Fin (N + 1), x χ i ^ 2

/-- Positive semidefiniteness of the visible block Toeplitz truncation. -/
def xi_cp_visible_implies_kappa0_block_psd
    (m N : ℕ) (c : Fin (m + 1) → ℝ) : Prop :=
  ∀ x : Fin (m + 1) → Fin (N + 1) → ℝ,
    0 ≤ xi_cp_visible_implies_kappa0_block_quadratic m N c x

/-- Concrete CP visible data: channel weights together with positive semidefinite block Toeplitz
truncations at every finite level. -/
structure xi_cp_visible_implies_kappa0_data (m : ℕ) where
  channelWeight : Fin (m + 1) → ℝ
  cpBlockToeplitzPsd :
    ∀ N : ℕ, xi_cp_visible_implies_kappa0_block_psd m N channelWeight

/-- The scalar Toeplitz quadratic form extracted from one visible channel. -/
def xi_cp_visible_implies_kappa0_scalar_quadratic
    (N : ℕ) (r : ℝ) (y : Fin (N + 1) → ℝ) : ℝ :=
  r * ∑ i : Fin (N + 1), y i ^ 2

/-- Positive semidefiniteness of one scalar visible channel. -/
def xi_cp_visible_implies_kappa0_scalar_psd (N : ℕ) (r : ℝ) : Prop :=
  ∀ y : Fin (N + 1) → ℝ, 0 ≤ xi_cp_visible_implies_kappa0_scalar_quadratic N r y

/-- Embed a scalar test vector into a single visible channel. -/
def xi_cp_visible_implies_kappa0_channel_extraction
    (m N : ℕ) (χ : Fin (m + 1)) (y : Fin (N + 1) → ℝ) :
    Fin (m + 1) → Fin (N + 1) → ℝ :=
  fun ψ i => if ψ = χ then y i else 0

/-- The visible negative-square index in this finite-channel model. -/
noncomputable def xi_cp_visible_implies_kappa0_visible_negative_square_index
    (m : ℕ) (D : xi_cp_visible_implies_kappa0_data m) : ℕ :=
  by
    classical
    exact
      if ∀ N : ℕ, ∀ χ : Fin (m + 1),
          xi_cp_visible_implies_kappa0_scalar_psd N (D.channelWeight χ) then
        0
      else
        1

/-- The concrete conclusion: every visible channel is PSD, hence the visible negative-square
index is zero. -/
def xi_cp_visible_implies_kappa0_statement
    (m : ℕ) (D : xi_cp_visible_implies_kappa0_data m) : Prop :=
  (∀ N : ℕ, ∀ χ : Fin (m + 1),
      xi_cp_visible_implies_kappa0_scalar_psd N (D.channelWeight χ)) ∧
    xi_cp_visible_implies_kappa0_visible_negative_square_index m D = 0

lemma xi_cp_visible_implies_kappa0_block_to_scalar
    (m N : ℕ) (D : xi_cp_visible_implies_kappa0_data m)
    (χ : Fin (m + 1)) :
    xi_cp_visible_implies_kappa0_scalar_psd N (D.channelWeight χ) := by
  intro y
  have hblock :=
    D.cpBlockToeplitzPsd N
      (xi_cp_visible_implies_kappa0_channel_extraction m N χ y)
  simpa [xi_cp_visible_implies_kappa0_block_psd,
    xi_cp_visible_implies_kappa0_block_quadratic,
    xi_cp_visible_implies_kappa0_scalar_psd,
    xi_cp_visible_implies_kappa0_scalar_quadratic,
    xi_cp_visible_implies_kappa0_channel_extraction] using hblock

/-- Paper label: `thm:xi-cp-visible-implies-kappa0`. -/
theorem paper_xi_cp_visible_implies_kappa0
    (m : ℕ) (D : xi_cp_visible_implies_kappa0_data m) :
    xi_cp_visible_implies_kappa0_statement m D := by
  have hchannels :
      ∀ N : ℕ, ∀ χ : Fin (m + 1),
        xi_cp_visible_implies_kappa0_scalar_psd N (D.channelWeight χ) := by
    intro N χ
    exact xi_cp_visible_implies_kappa0_block_to_scalar m N D χ
  refine ⟨hchannels, ?_⟩
  simp [xi_cp_visible_implies_kappa0_visible_negative_square_index, hchannels]

end Omega.Zeta
