import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The Cayley map sending the upper half-plane to the unit disk and `t → ±∞` to `-1`. -/
def appCayleyUpperHalfMap (t : ℂ) : ℂ :=
  (Complex.I - t) / (Complex.I + t)

/-- Explicit inverse of the Cayley map away from `-1`. -/
def appCayleyUpperHalfInv (z : ℂ) : ℂ :=
  Complex.I * (1 - z) / (1 + z)

lemma appCayleyUpperHalf_left_inv {t : ℂ} (ht : t ≠ -Complex.I) :
    appCayleyUpperHalfInv (appCayleyUpperHalfMap t) = t := by
  have hden : Complex.I + t ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero, add_comm] using ht
  unfold appCayleyUpperHalfInv appCayleyUpperHalfMap
  field_simp [hden]
  ring

lemma appCayleyUpperHalf_right_inv {z : ℂ} (hz : z ≠ -(1 : ℂ)) :
    appCayleyUpperHalfMap (appCayleyUpperHalfInv z) = z := by
  have hden : 1 + z ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero, add_comm] using hz
  unfold appCayleyUpperHalfInv appCayleyUpperHalfMap
  field_simp [hden]
  ring

lemma appCayleyUpperHalf_normSq_formula (x y : ℝ) :
    Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + y * Complex.I)) =
      (x ^ 2 + (1 - y) ^ 2) / (x ^ 2 + (1 + y) ^ 2) := by
  unfold appCayleyUpperHalfMap
  rw [Complex.normSq_div]
  have hnum :
      Complex.normSq (Complex.I - ((x : ℂ) + y * Complex.I)) = x ^ 2 + (1 - y) ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  have hden :
      Complex.normSq (Complex.I + ((x : ℂ) + y * Complex.I)) = x ^ 2 + (1 + y) ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  rw [hnum, hden]

lemma appCayleyUpperHalf_normSq_lt_one (x y : ℝ) (hy : 0 < y) :
    Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + y * Complex.I)) < 1 := by
  rw [appCayleyUpperHalf_normSq_formula]
  have hpos : 0 < x ^ 2 + (1 + y) ^ 2 := by positivity
  refine (div_lt_one hpos).2 ?_
  nlinarith [sq_nonneg x, sq_nonneg (1 - y), sq_nonneg (1 + y)]

lemma appCayleyUpperHalf_normSq_eq_one (x : ℝ) :
    Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + (0 : ℝ) * Complex.I)) = 1 := by
  rw [appCayleyUpperHalf_normSq_formula]
  field_simp
  ring

/-- Concrete certificate for the Cayley upper-half-plane / disk correspondence. -/
def AppCayleyUpperhalfDiskStatement : Prop :=
  (∀ t : ℂ, t ≠ -Complex.I → appCayleyUpperHalfInv (appCayleyUpperHalfMap t) = t) ∧
    (∀ z : ℂ, z ≠ -(1 : ℂ) → appCayleyUpperHalfMap (appCayleyUpperHalfInv z) = z) ∧
    (∀ x y : ℝ,
      Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + y * Complex.I)) =
        (x ^ 2 + (1 - y) ^ 2) / (x ^ 2 + (1 + y) ^ 2)) ∧
    (∀ x y : ℝ, 0 < y → Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + y * Complex.I)) < 1) ∧
    (∀ x : ℝ, Complex.normSq (appCayleyUpperHalfMap ((x : ℂ) + (0 : ℝ) * Complex.I)) = 1)

theorem appCayleyUpperhalfDiskCertificate : AppCayleyUpperhalfDiskStatement := by
  refine ⟨?_, ?_, appCayleyUpperHalf_normSq_formula, appCayleyUpperHalf_normSq_lt_one,
    appCayleyUpperHalf_normSq_eq_one⟩
  · intro t ht
    exact appCayleyUpperHalf_left_inv ht
  · intro z hz
    exact appCayleyUpperHalf_right_inv hz

/-- Paper label: `prop:app-cayley-upperhalf-disk`. -/
theorem paper_app_cayley_upperhalf_disk : AppCayleyUpperhalfDiskStatement := by
  exact appCayleyUpperhalfDiskCertificate

end

end Omega.UnitCirclePhaseArithmetic
