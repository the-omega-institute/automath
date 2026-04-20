import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Complex

/-- The window-`6` size-biased fiber law supported on the atoms `2, 3, 4`. -/
def window6BiasedFiberMass : ℕ → ℚ
  | 2 => 1 / 4
  | 3 => 3 / 16
  | 4 => 9 / 16
  | _ => 0

/-- The Cauchy--Stieltjes transform of the window-`6` size-biased fiber law. -/
noncomputable def window6G (z : ℂ) : ℂ :=
  ((1 / 4 : ℝ) : ℂ) / (z - 2) + ((3 / 16 : ℝ) : ℂ) / (z - 3) + ((9 / 16 : ℝ) : ℂ) / (z - 4)

/-- The Herglotz companion transform `M₆(z) = -G₆(z) = ∫ (t - z)⁻¹ dν₆(t)`. -/
noncomputable def window6M (z : ℂ) : ℂ :=
  ((1 / 4 : ℝ) : ℂ) / (2 - z) + ((3 / 16 : ℝ) : ℂ) / (3 - z) + ((9 / 16 : ℝ) : ℂ) / (4 - z)

/-- The moments of the size-biased law. -/
def window6Moment (n : ℕ) : ℚ :=
  (1 / 4 : ℚ) * 2 ^ n + (3 / 16 : ℚ) * 3 ^ n + (9 / 16 : ℚ) * 4 ^ n

/-- Concrete closed-form package for the window-`6` biased fiber law. -/
def xiWindow6MicrostateBiasedFiberlawHerglotzClosedform : Prop :=
  window6BiasedFiberMass 2 = 1 / 4 ∧
    window6BiasedFiberMass 3 = 3 / 16 ∧
    window6BiasedFiberMass 4 = 9 / 16 ∧
    window6BiasedFiberMass 2 + window6BiasedFiberMass 3 + window6BiasedFiberMass 4 = 1 ∧
    (∀ z : ℂ, z ≠ 2 → z ≠ 3 → z ≠ 4 →
      window6G z =
        ((16 : ℂ) * z ^ 2 - 91 * z + 126) / (16 * (z - 2) * (z - 3) * (z - 4))) ∧
    (∀ n : ℕ, window6Moment n = (8 * 2 ^ (n + 1) + 4 * 3 ^ (n + 1) + 9 * 4 ^ (n + 1)) / 64) ∧
    (∀ z : ℂ, 0 < z.im → 0 < (window6M z).im)

private lemma sub_real_ne_zero_of_im_pos (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ((t : ℂ) - z) ≠ 0 := by
  intro h
  have him : (((t : ℂ) - z).im) = 0 := by simp [h]
  simp [Complex.sub_im] at him
  linarith

private lemma atom_im_pos (w t : ℝ) (hw : 0 < w) {z : ℂ} (hz : 0 < z.im) :
    0 < Complex.im (((w : ℂ) / ((t : ℂ) - z)) : ℂ) := by
  have hz_ne : ((t : ℂ) - z) ≠ 0 := sub_real_ne_zero_of_im_pos t hz
  have hnorm : 0 < Complex.normSq ((t : ℂ) - z) := Complex.normSq_pos.2 hz_ne
  have him :
      Complex.im (((w : ℂ) / ((t : ℂ) - z) : ℂ)) =
        w * z.im / Complex.normSq ((t : ℂ) - z) := by
    rw [Complex.div_im]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  rw [him]
  exact div_pos (mul_pos hw hz) hnorm

/-- The window-`6` biased law is the explicit measure
`(1/4)δ₂ + (3/16)δ₃ + (9/16)δ₄`; its Cauchy transform is a rational function with numerator
`16 z² - 91 z + 126`, its moments have the stated closed form, and the companion transform is
Herglotz on the upper half-plane.
    thm:xi-time-part9zc-window6-microstate-biased-fiberlaw-herglotz-closedform -/
theorem paper_xi_time_part9zc_window6_microstate_biased_fiberlaw_herglotz_closedform :
    xiWindow6MicrostateBiasedFiberlawHerglotzClosedform := by
  refine ⟨rfl, rfl, rfl, by norm_num [window6BiasedFiberMass], ?_, ?_, ?_⟩
  · intro z hz2 hz3 hz4
    have hz2' : z - 2 ≠ 0 := sub_ne_zero.mpr hz2
    have hz3' : z - 3 ≠ 0 := sub_ne_zero.mpr hz3
    have hz4' : z - 4 ≠ 0 := sub_ne_zero.mpr hz4
    unfold window6G
    field_simp [hz2', hz3', hz4']
    norm_num
    ring
  · intro n
    unfold window6Moment
    norm_num [pow_succ, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  · intro z hz
    unfold window6M
    have h2 : 0 < Complex.im ((((1 / 4 : ℝ) : ℂ) / (2 - z) : ℂ)) :=
      atom_im_pos (1 / 4 : ℝ) 2 (by norm_num) hz
    have h3 : 0 < Complex.im ((((3 / 16 : ℝ) : ℂ) / (3 - z) : ℂ)) :=
      atom_im_pos (3 / 16 : ℝ) 3 (by norm_num) hz
    have h4 : 0 < Complex.im ((((9 / 16 : ℝ) : ℂ) / (4 - z) : ℂ)) :=
      atom_im_pos (9 / 16 : ℝ) 4 (by norm_num) hz
    have him :
        Complex.im (window6M z) =
          Complex.im ((((1 / 4 : ℝ) : ℂ) / (2 - z) : ℂ)) +
            Complex.im ((((3 / 16 : ℝ) : ℂ) / (3 - z) : ℂ)) +
              Complex.im ((((9 / 16 : ℝ) : ℂ) / (4 - z) : ℂ)) := by
      simp [window6M, add_assoc]
    have hsum :
        0 <
          Complex.im ((((1 / 4 : ℝ) : ℂ) / (2 - z) : ℂ)) +
            Complex.im ((((3 / 16 : ℝ) : ℂ) / (3 - z) : ℂ)) +
              Complex.im ((((9 / 16 : ℝ) : ℂ) / (4 - z) : ℂ)) := by
      linarith
    simpa [him] using hsum

end Omega.Zeta
