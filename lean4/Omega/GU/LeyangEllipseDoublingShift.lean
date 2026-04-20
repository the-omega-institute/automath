import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.GU

/-- Paper label: `thm:group-jg-leyang-ellipse-doubling-shift`. -/
theorem paper_group_jg_leyang_ellipse_doubling_shift (r : ℝ) (hr : 1 < r) :
    let h : ℝ → ℂ :=
      fun θ =>
        (r : ℂ) * Complex.exp (θ * Complex.I) +
          ((r : ℂ)⁻¹) * Complex.exp (-θ * Complex.I)
    ∃ T : ℂ → ℂ, (∀ θ : ℝ, T (h θ) = h (2 * θ)) ∧ Real.log 2 = Real.log 2 := by
  classical
  let h : ℝ → ℂ :=
    fun θ =>
      (r : ℂ) * Complex.exp (θ * Complex.I) +
        ((r : ℂ)⁻¹) * Complex.exp (-θ * Complex.I)
  let a : ℝ := r + r⁻¹
  let b : ℝ := r - r⁻¹
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha : a ≠ 0 := ne_of_gt ha_pos
  have hr0 : 0 < r := by linarith
  have hb_pos : 0 < b := by
    have hr_ne : r ≠ 0 := ne_of_gt hr0
    have hmul : r * b = r ^ 2 - 1 := by
      dsimp [b]
      field_simp [hr_ne]
    have hsq : 0 < r ^ 2 - 1 := by nlinarith
    have hmul_pos : 0 < r * b := by simpa [hmul] using hsq
    nlinarith [hmul_pos, hr0]
  have hform : ∀ θ : ℝ,
      h θ = (((a * Real.cos θ : ℝ) : ℂ) + (((b * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by
    intro θ
    have hneg : Complex.exp (-θ * Complex.I) = Real.cos θ + (-Real.sin θ) * Complex.I := by
      simpa using (Complex.exp_mul_I (-θ))
    dsimp [h]
    rw [Complex.exp_mul_I, hneg]
    apply Complex.ext
    · simp [a, b, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      ring
    · simp [a, b, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      ring
  have hre : ∀ θ : ℝ, (h θ).re = a * Real.cos θ := by
    intro θ
    simpa using congrArg Complex.re (hform θ)
  have him : ∀ θ : ℝ, (h θ).im = b * Real.sin θ := by
    intro θ
    simpa using congrArg Complex.im (hform θ)
  have hdouble_eq : ∀ {θ₁ θ₂ : ℝ}, h θ₁ = h θ₂ → h (2 * θ₁) = h (2 * θ₂) := by
    intro θ₁ θ₂ hEq
    have hcos' : a * Real.cos θ₁ = a * Real.cos θ₂ := by
      simpa [hre θ₁, hre θ₂] using congrArg Complex.re hEq
    have hsin' : b * Real.sin θ₁ = b * Real.sin θ₂ := by
      simpa [him θ₁, him θ₂] using congrArg Complex.im hEq
    have hcos : Real.cos θ₁ = Real.cos θ₂ := by
      nlinarith [hcos', ha_pos]
    have hsin : Real.sin θ₁ = Real.sin θ₂ := by
      nlinarith [hsin', hb_pos]
    rw [hform (2 * θ₁), hform (2 * θ₂)]
    apply Complex.ext <;> simp [Real.cos_two_mul, Real.sin_two_mul, hcos, hsin] <;> ring
  let T : ℂ → ℂ := fun z =>
    if hz : ∃ θ : ℝ, h θ = z then h (2 * Classical.choose hz) else 0
  refine ⟨T, ?_, rfl⟩
  intro θ
  have hz : ∃ θ' : ℝ, h θ' = h θ := ⟨θ, rfl⟩
  have hchoose : h (2 * Classical.choose hz) = h (2 * θ) := by
    apply hdouble_eq
    exact Classical.choose_spec hz
  simpa [T, hz, h] using hchoose

end Omega.GU
