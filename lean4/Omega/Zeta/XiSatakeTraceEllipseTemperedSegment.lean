import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
import Omega.Zeta.PhaseLiftSpectralBound
import Omega.Zeta.XiCayleyJoukowskyHarmonicMeasureEllipse

namespace Omega.Zeta

noncomputable section

/-- The Satake trace coordinate `S(\alpha) = \alpha + \alpha^{-1}`. -/
def xi_satake_trace_ellipse_tempered_segment_trace (α : ℂ) : ℂ :=
  α + α⁻¹

/-- Paper label: `prop:xi-satake-trace-ellipse-tempered-segment`. The existing Joukowsky theorem
already gives the ellipse parameterization corresponding to `\alpha = \sqrt L\,e^{i\theta}`; on
the tempered slice `L = 1`, the Satake trace is `2 cos θ`, hence the image is exactly `[-2,2]`. -/
theorem paper_xi_satake_trace_ellipse_tempered_segment :
    (∀ L θ : ℝ,
      xiJoukowskyX L θ = xiEllipseA L * Real.cos θ ∧
        xiJoukowskyY L θ = xiEllipseB L * Real.sin θ) ∧
    (∀ θ : ℝ,
      xi_satake_trace_ellipse_tempered_segment_trace (Complex.exp (θ * Complex.I)) =
        (2 * Real.cos θ : ℂ)) ∧
    (∀ x : ℝ,
      x ∈ Set.Icc (-2) 2 ↔
        ∃ α : ℂ, ‖α‖ = 1 ∧ xi_satake_trace_ellipse_tempered_segment_trace α = (x : ℂ)) := by
  have hellipse := paper_xi_cayley_joukowsky_harmonic_measure_ellipse
  refine ⟨?_, ?_, ?_⟩
  · intro L θ
    exact ⟨(hellipse.2.1 L θ).1, (hellipse.2.1 L θ).2.1⟩
  · intro θ
    unfold xi_satake_trace_ellipse_tempered_segment_trace
    have hexp_inv : (Complex.exp (θ * Complex.I))⁻¹ = Complex.exp (-θ * Complex.I) := by
      apply inv_eq_of_mul_eq_one_right
      calc
        Complex.exp (θ * Complex.I) * Complex.exp (-θ * Complex.I)
            = Complex.exp (θ * Complex.I + -θ * Complex.I) := by
                rw [← Complex.exp_add]
        _ = Complex.exp 0 := by
              congr 1
              ring
        _ = 1 := by simp
    have hneg_exp :
        Complex.exp (-θ * Complex.I) = Real.cos θ - Real.sin θ * Complex.I := by
      simpa [neg_mul, Complex.exp_mul_I] using (Complex.exp_mul_I (-θ))
    calc
      Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹
          = Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I) := by rw [hexp_inv]
      _ = (Real.cos θ + Real.sin θ * Complex.I) + (Real.cos θ - Real.sin θ * Complex.I) := by
            rw [Complex.exp_mul_I, hneg_exp, ← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
      _ = (2 * Real.cos θ : ℂ) := by
            ring
  · intro x
    constructor
    · intro hx
      rcases (paper_phase_lift_spectral_bound.1 x hx) with ⟨hu, htrace⟩
      exact ⟨phase_lift_spectral_bound_phase x, hu, htrace⟩
    · rintro ⟨α, hαunit, htrace⟩
      rcases (paper_phase_lift_spectral_bound.2 α hαunit) with ⟨y, hy, hytrace⟩
      rw [xi_satake_trace_ellipse_tempered_segment_trace] at htrace
      have hxy_complex : (x : ℂ) = (y : ℂ) := by
        rw [← htrace, hytrace]
      have hxy : x = y := by
        exact_mod_cast (congrArg Complex.re hxy_complex)
      simpa [hxy] using hy

end

end Omega.Zeta
