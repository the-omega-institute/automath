import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Coefficientwise rotation by the unit complex number `ω`. -/
def abel_character_spectrum_as_rotation_correlation_rotation {n : ℕ} (ω : ℂ)
    (coeff : Fin n → ℂ) : Fin n → ℂ :=
  fun k => star (ω ^ k.1) * coeff k

/-- The finite-dimensional Hardy-style inner product used in this local model. -/
def abel_character_spectrum_as_rotation_correlation_inner {n : ℕ} (f g : Fin n → ℂ) : ℂ :=
  ∑ k, f k * star (g k)

/-- The weighted power series attached to the coefficient package. -/
def abel_character_spectrum_as_rotation_correlation_weighted_series {n : ℕ} (ω : ℂ)
    (coeff : Fin n → ℂ) : ℂ :=
  ∑ k, (coeff k * star (coeff k)) * ω ^ k.1

/-- The normalized character coefficient extracted from the weighted series. -/
def abel_character_spectrum_as_rotation_correlation_normalized_character {n : ℕ} (ω : ℂ)
    (a : ℕ) (coeff : Fin n → ℂ) : ℂ :=
  abel_character_spectrum_as_rotation_correlation_weighted_series (ω ^ a) coeff /
    abel_character_spectrum_as_rotation_correlation_inner coeff coeff

/-- Rotation preserves the local energy. -/
def abel_character_spectrum_as_rotation_correlation_rotation_is_unitary {n : ℕ} (ω : ℂ)
    (coeff : Fin n → ℂ) : Prop :=
  abel_character_spectrum_as_rotation_correlation_inner
      (abel_character_spectrum_as_rotation_correlation_rotation ω coeff)
      (abel_character_spectrum_as_rotation_correlation_rotation ω coeff) =
    abel_character_spectrum_as_rotation_correlation_inner coeff coeff

/-- The rotation correlation expands as the weighted power series. -/
def abel_character_spectrum_as_rotation_correlation_rotation_correlation_formula {n : ℕ}
    (ω : ℂ) (coeff : Fin n → ℂ) : Prop :=
  abel_character_spectrum_as_rotation_correlation_inner coeff
      (abel_character_spectrum_as_rotation_correlation_rotation ω coeff) =
    abel_character_spectrum_as_rotation_correlation_weighted_series ω coeff

/-- Additive characters are realized as normalized rotation correlations. -/
def abel_character_spectrum_as_rotation_correlation_normalized_character_formula {n : ℕ}
    (ω : ℂ) (a : ℕ) (coeff : Fin n → ℂ) : Prop :=
  abel_character_spectrum_as_rotation_correlation_normalized_character ω a coeff =
    abel_character_spectrum_as_rotation_correlation_inner coeff
        (abel_character_spectrum_as_rotation_correlation_rotation (ω ^ a) coeff) /
      abel_character_spectrum_as_rotation_correlation_inner coeff coeff

private lemma abel_character_spectrum_as_rotation_correlation_pow_unit (ω : ℂ)
    (hω : ω * star ω = 1) (k : ℕ) :
    star (ω ^ k) * ω ^ k = 1 := by
  calc
    star (ω ^ k) * ω ^ k = star ω ^ k * ω ^ k := by
      simp
    _ = (star ω * ω) ^ k := by
      rw [← mul_pow]
    _ = 1 := by
      have hω' : star ω * ω = 1 := by simpa [mul_comm] using hω
      rw [hω']
      simp

private lemma abel_character_spectrum_as_rotation_correlation_correlation_formula_aux {n : ℕ}
    (ω : ℂ) (coeff : Fin n → ℂ) :
    abel_character_spectrum_as_rotation_correlation_rotation_correlation_formula ω coeff := by
  unfold abel_character_spectrum_as_rotation_correlation_rotation_correlation_formula
  unfold abel_character_spectrum_as_rotation_correlation_inner
  unfold abel_character_spectrum_as_rotation_correlation_weighted_series
  refine Finset.sum_congr rfl ?_
  intro k _
  dsimp [abel_character_spectrum_as_rotation_correlation_rotation]
  simp
  ring_nf

/-- Paper label: `prop:abel-character-spectrum-as-rotation-correlation`.
In the finite-dimensional Hardy coefficient model, unit-modulus rotations are unitary, their
correlations expand coefficientwise, and additive characters are the corresponding normalized
rotation correlations. -/
theorem paper_abel_character_spectrum_as_rotation_correlation {n : ℕ} (ω : ℂ)
    (hω : ω * star ω = 1) (a : ℕ) (coeff : Fin n → ℂ) :
    abel_character_spectrum_as_rotation_correlation_rotation_is_unitary ω coeff ∧
      abel_character_spectrum_as_rotation_correlation_rotation_correlation_formula ω coeff ∧
      abel_character_spectrum_as_rotation_correlation_normalized_character_formula ω a coeff := by
  have hcorr :
      ∀ ζ : ℂ,
        abel_character_spectrum_as_rotation_correlation_rotation_correlation_formula ζ coeff := by
    intro ζ
    exact abel_character_spectrum_as_rotation_correlation_correlation_formula_aux ζ coeff
  refine ⟨?_, hcorr ω, ?_⟩
  · unfold abel_character_spectrum_as_rotation_correlation_rotation_is_unitary
    unfold abel_character_spectrum_as_rotation_correlation_inner
    refine Finset.sum_congr rfl ?_
    intro k _
    dsimp [abel_character_spectrum_as_rotation_correlation_rotation]
    calc
      star (ω ^ k.1) * coeff k * star (star (ω ^ k.1) * coeff k) =
          (star (ω ^ k.1) * ω ^ k.1) * (coeff k * star (coeff k)) := by
            simp
            ring_nf
      _ = coeff k * star (coeff k) := by
        rw [abel_character_spectrum_as_rotation_correlation_pow_unit ω hω k.1]
        simp
  · unfold abel_character_spectrum_as_rotation_correlation_normalized_character_formula
    unfold abel_character_spectrum_as_rotation_correlation_normalized_character
    rw [hcorr (ω ^ a)]

end

end Omega.Zeta
