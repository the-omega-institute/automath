import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The pointwise phase lift attached to a spectral value `x ∈ [-2,2]`. -/
def phase_lift_spectral_bound_phase (x : ℝ) : ℂ :=
  Complex.exp (Real.arccos (x / 2) * Complex.I)

/-- Paper label: `thm:phase-lift-spectral-bound`. Pointwise on the spectral interval `[-2,2]`,
the explicit phase lift `exp(i arccos(x / 2))` lies on the unit circle and satisfies
`x = u + u⁻¹`; conversely any unit-modulus phase produces a real point of `[-2,2]` via the same
Joukowsky map. -/
theorem paper_phase_lift_spectral_bound :
    (∀ x : ℝ, x ∈ Set.Icc (-2) 2 →
      let u := phase_lift_spectral_bound_phase x
      ‖u‖ = 1 ∧ u + u⁻¹ = (x : ℂ)) ∧
    (∀ u : ℂ, ‖u‖ = 1 →
      ∃ x : ℝ, x ∈ Set.Icc (-2) 2 ∧ u + u⁻¹ = (x : ℂ)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    let θ : ℝ := Real.arccos (x / 2)
    let s : ℝ := Real.sqrt (1 - (x / 2) ^ 2)
    let u : ℂ := phase_lift_spectral_bound_phase x
    have hx_left : -1 ≤ x / 2 := by nlinarith [hx.1]
    have hx_right : x / 2 ≤ 1 := by nlinarith [hx.2]
    have hu_norm : ‖u‖ = 1 := by
      simp [u, phase_lift_spectral_bound_phase, Complex.norm_exp_ofReal_mul_I]
    have hu_eq : u = (x / 2 : ℂ) + Complex.I * s := by
      calc
        u = Real.cos θ + Real.sin θ * Complex.I := by
          simp [u, phase_lift_spectral_bound_phase, θ, Complex.exp_mul_I]
        _ = (x / 2 : ℂ) + Complex.I * s := by
          simp [θ, s, Real.cos_arccos hx_left hx_right, Real.sin_arccos, mul_comm]
    have hu_inv_exp : u⁻¹ = Complex.exp (-θ * Complex.I) := by
      dsimp [u, θ]
      apply inv_eq_of_mul_eq_one_right
      calc
        Complex.exp (↑(Real.arccos (x / 2)) * Complex.I) * Complex.exp (-↑(Real.arccos (x / 2)) * Complex.I)
            = Complex.exp
                (↑(Real.arccos (x / 2)) * Complex.I + -↑(Real.arccos (x / 2)) * Complex.I) := by
                  rw [← Complex.exp_add]
        _ = Complex.exp 0 := by
              congr 1
              ring
        _ = 1 := by simp
    have hu_inv : u⁻¹ = (x / 2 : ℂ) - Complex.I * s := by
      calc
        u⁻¹ = Complex.exp (-θ * Complex.I) := hu_inv_exp
        _ = Real.cos θ - Real.sin θ * Complex.I := by
              simpa [neg_mul, Complex.exp_mul_I] using Complex.exp_mul_I (-θ)
        _ = (x / 2 : ℂ) - Complex.I * s := by
              simp [θ, s, Real.cos_arccos hx_left hx_right, Real.sin_arccos, mul_comm]
    refine ⟨hu_norm, ?_⟩
    calc
      u + u⁻¹ = u + ((x / 2 : ℂ) - Complex.I * s) := by rw [hu_inv]
      _ = ((x / 2 : ℂ) + Complex.I * s) + ((x / 2 : ℂ) - Complex.I * s) := by rw [hu_eq]
      _ = (x : ℂ) := by ring
  · intro u hu
    refine ⟨2 * u.re, ?_, ?_⟩
    · have hre_abs : |u.re| ≤ 1 := by
        simpa [hu] using (Complex.abs_re_le_norm u)
      rcases abs_le.mp hre_abs with ⟨hre_left, hre_right⟩
      constructor <;> nlinarith
    · apply Complex.ext
      · simp [Complex.add_re, Complex.inv_re, Complex.normSq_eq_norm_sq, hu, two_mul]
      · simp [Complex.add_im, Complex.inv_im, Complex.normSq_eq_norm_sq, hu]

end

end Omega.Zeta
