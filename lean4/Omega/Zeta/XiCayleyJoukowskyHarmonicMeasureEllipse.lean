import Mathlib

namespace Omega.Zeta

/-- The Cauchy density on the line. -/
noncomputable def xiCauchyDensity (x : ℝ) : ℝ :=
  1 / (Real.pi * (1 + x ^ 2))

/-- The angle density obtained from the Cayley coordinate change `θ = 2 arctan x`. -/
noncomputable def xiUniformAngleDensityFromCayley (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (2 / (1 + x ^ 2))

/-- Semi-major axis of the Joukowsky ellipse. -/
noncomputable def xiEllipseA (L : ℝ) : ℝ :=
  Real.sqrt L + 1 / Real.sqrt L

/-- Semi-minor axis of the Joukowsky ellipse. -/
noncomputable def xiEllipseB (L : ℝ) : ℝ :=
  Real.sqrt L - 1 / Real.sqrt L

/-- Real part of `J_L(e^{iθ}) = √L e^{iθ} + L^{-1/2} e^{-iθ}`. -/
noncomputable def xiJoukowskyX (L θ : ℝ) : ℝ :=
  Real.sqrt L * Real.cos θ + (1 / Real.sqrt L) * Real.cos θ

/-- Imaginary part of `J_L(e^{iθ}) = √L e^{iθ} + L^{-1/2} e^{-iθ}`. -/
noncomputable def xiJoukowskyY (L θ : ℝ) : ℝ :=
  Real.sqrt L * Real.sin θ - (1 / Real.sqrt L) * Real.sin θ

/-- The arc-speed of the ellipse parameterization. -/
noncomputable def xiEllipseArcSpeed (L θ : ℝ) : ℝ :=
  Real.sqrt ((-xiEllipseA L * Real.sin θ) ^ 2 + (xiEllipseB L * Real.cos θ) ^ 2)

/-- The limiting arcsine density on `[-2, 2]`. -/
noncomputable def xiArcsineDensity (x : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (4 - x ^ 2))

private theorem xiCayley_pushes_cauchy_to_uniform (x : ℝ) :
    xiUniformAngleDensityFromCayley x = xiCauchyDensity x := by
  have hx : (1 + x ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg x]
  unfold xiUniformAngleDensityFromCayley xiCauchyDensity
  field_simp [Real.pi_ne_zero, hx]

private theorem xiJoukowsky_parametrization (L θ : ℝ) :
    xiJoukowskyX L θ = xiEllipseA L * Real.cos θ ∧
      xiJoukowskyY L θ = xiEllipseB L * Real.sin θ := by
  constructor
  · unfold xiJoukowskyX xiEllipseA
    ring
  · unfold xiJoukowskyY xiEllipseB
    ring

private theorem xiJoukowsky_arc_speed_formula (L θ : ℝ) :
    xiEllipseArcSpeed L θ =
      Real.sqrt (xiEllipseA L ^ 2 * Real.sin θ ^ 2 + xiEllipseB L ^ 2 * Real.cos θ ^ 2) := by
  unfold xiEllipseArcSpeed
  congr 1
  ring

private theorem xiJoukowsky_degenerates_to_segment (θ : ℝ) :
    xiJoukowskyX 1 θ = 2 * Real.cos θ ∧ xiJoukowskyY 1 θ = 0 := by
  constructor
  · unfold xiJoukowskyX
    simp
    ring
  · unfold xiJoukowskyY
    simp

private theorem xiArcsine_change_of_variables (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    xiArcsineDensity (xiJoukowskyX 1 θ) * (2 * |Real.sin θ|) = 1 / Real.pi := by
  have hx : xiJoukowskyX 1 θ = 2 * Real.cos θ := (xiJoukowsky_degenerates_to_segment θ).1
  rw [hx, xiArcsineDensity]
  have hsqrt : Real.sqrt (4 - (2 * Real.cos θ) ^ 2) = 2 * |Real.sin θ| := by
    have hsq : 4 - (2 * Real.cos θ) ^ 2 = (2 * Real.sin θ) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt]
  have hs : (2 : ℝ) * |Real.sin θ| ≠ 0 := by
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr hsin)
  field_simp [Real.pi_ne_zero, hs]

/-- Symbolic Cayley--Joukowsky package: the Cayley density change reproduces the Cauchy law, the
Joukowsky map yields the ellipse parameterization and arc-speed density, and at `L = 1` the ellipse
degenerates to `[-2, 2]` with the arcsine density after the standard change of variables.
    thm:xi-cayley-joukowsky-harmonic-measure-ellipse -/
theorem paper_xi_cayley_joukowsky_harmonic_measure_ellipse :
    (∀ x : ℝ, xiUniformAngleDensityFromCayley x = xiCauchyDensity x) ∧
      (∀ L θ : ℝ,
        xiJoukowskyX L θ = xiEllipseA L * Real.cos θ ∧
          xiJoukowskyY L θ = xiEllipseB L * Real.sin θ ∧
          xiEllipseArcSpeed L θ =
            Real.sqrt (xiEllipseA L ^ 2 * Real.sin θ ^ 2 +
              xiEllipseB L ^ 2 * Real.cos θ ^ 2)) ∧
      (∀ θ : ℝ, xiJoukowskyX 1 θ = 2 * Real.cos θ ∧ xiJoukowskyY 1 θ = 0) ∧
      (∀ θ : ℝ, Real.sin θ ≠ 0 →
        xiArcsineDensity (xiJoukowskyX 1 θ) * (2 * |Real.sin θ|) = 1 / Real.pi) := by
  refine ⟨xiCayley_pushes_cauchy_to_uniform, ?_, xiJoukowsky_degenerates_to_segment,
    xiArcsine_change_of_variables⟩
  intro L θ
  refine ⟨(xiJoukowsky_parametrization L θ).1, (xiJoukowsky_parametrization L θ).2,
    xiJoukowsky_arc_speed_formula L θ⟩

end Omega.Zeta
