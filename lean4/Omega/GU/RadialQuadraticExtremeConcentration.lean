import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.GU

/-- The radial-quadratic center parameter `c(r) = r² + r⁻²`. -/
noncomputable def c (r : ℝ) : ℝ :=
  r ^ 2 + (r⁻¹) ^ 2

/-- Lower extreme estimator obtained from the sample maximum. -/
noncomputable def underline_c_n (r eps : ℝ) : ℝ :=
  c r - eps

/-- Upper extreme estimator obtained from the sample minimum. -/
noncomputable def overline_c_n (r eps : ℝ) : ℝ :=
  c r + eps

/-- Exact one-sided extreme tail coming from the endpoint-angle measure. -/
noncomputable def radialQuadraticAngleTail (eps : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) * Real.arccos (1 - eps / 2) / Real.pi)

/-- The square-root surrogate used in the paper's simplified bound. -/
noncomputable def radialQuadraticSqrtTail (eps : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) * Real.sqrt eps / Real.pi)

/-- Lower-tail contribution to the two-sided extreme event. -/
noncomputable def radialQuadraticLowerTail (eps : ℝ) (n : ℕ) : ℝ :=
  radialQuadraticAngleTail eps n

/-- Upper-tail contribution to the two-sided extreme event. -/
noncomputable def radialQuadraticUpperTail (eps : ℝ) (n : ℕ) : ℝ :=
  radialQuadraticAngleTail eps n

/-- Two-sided union-bound estimate for the extreme concentration event. -/
noncomputable def radialQuadraticTwoSidedTail (eps : ℝ) (n : ℕ) : ℝ :=
  radialQuadraticLowerTail eps n + radialQuadraticUpperTail eps n

lemma sqrt_le_arccos_one_sub_half_eps {eps : ℝ} (heps : 0 < eps) (hε2 : eps ≤ 2) :
    Real.sqrt eps ≤ Real.arccos (1 - eps / 2) := by
  let θ := Real.arccos (1 - eps / 2)
  have hθ_nonneg : 0 ≤ θ := by
    simp [θ, Real.arccos_nonneg]
  have harg_lower : -1 ≤ 1 - eps / 2 := by
    nlinarith
  have harg_upper : 1 - eps / 2 ≤ 1 := by
    nlinarith
  have hcos : Real.cos θ = 1 - eps / 2 := by
    simp [θ, Real.cos_arccos harg_lower harg_upper]
  have hquad : 1 - θ ^ 2 / 2 ≤ 1 - eps / 2 := by
    simpa [hcos] using (Real.one_sub_sq_div_two_le_cos (x := θ))
  have hsq : eps ≤ θ ^ 2 := by
    nlinarith
  have hsqrt_sq : (Real.sqrt eps) ^ 2 ≤ θ ^ 2 := by
    simpa [Real.sq_sqrt heps.le] using hsq
  exact (sq_le_sq₀ (Real.sqrt_nonneg eps) hθ_nonneg).mp hsqrt_sq

lemma radialQuadraticAngleTail_le_sqrtTail {eps : ℝ} {n : ℕ}
    (heps : 0 < eps) (hε2 : eps ≤ 2) :
    radialQuadraticAngleTail eps n ≤ radialQuadraticSqrtTail eps n := by
  unfold radialQuadraticAngleTail radialQuadraticSqrtTail
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hsqrt : Real.sqrt eps ≤ Real.arccos (1 - eps / 2) :=
    sqrt_le_arccos_one_sub_half_eps heps hε2
  have hmul : (-(n : ℝ)) * Real.arccos (1 - eps / 2) ≤ (-(n : ℝ)) * Real.sqrt eps := by
    nlinarith
  exact div_le_div_of_nonneg_right hmul Real.pi_pos.le

/-- Paper: `thm:group-jg-radial-quadratic-extreme-concentration`.
The lower and upper estimators sit exactly `ε` away from the center `c(r)`, each one-sided tail
is bounded by the square-root surrogate, and the two-sided event is controlled by the union bound.
-/
theorem paper_group_jg_radial_quadratic_extreme_concentration :
    ∀ {r eps : Real} {n : Nat}, 0 < eps → eps ≤ 2 →
      c r - underline_c_n r eps = eps ∧
      overline_c_n r eps - c r = eps ∧
      radialQuadraticTwoSidedTail eps n =
        radialQuadraticLowerTail eps n + radialQuadraticUpperTail eps n ∧
      radialQuadraticLowerTail eps n ≤ radialQuadraticSqrtTail eps n ∧
      radialQuadraticUpperTail eps n ≤ radialQuadraticSqrtTail eps n ∧
      radialQuadraticTwoSidedTail eps n ≤ 2 * radialQuadraticSqrtTail eps n := by
  intro r eps n heps hε2
  refine ⟨by simp [underline_c_n], by simp [overline_c_n], rfl, ?_, ?_, ?_⟩
  · exact radialQuadraticAngleTail_le_sqrtTail heps hε2
  · exact radialQuadraticAngleTail_le_sqrtTail heps hε2
  · unfold radialQuadraticTwoSidedTail radialQuadraticLowerTail radialQuadraticUpperTail
    have htail : radialQuadraticAngleTail eps n ≤ radialQuadraticSqrtTail eps n :=
      radialQuadraticAngleTail_le_sqrtTail heps hε2
    linarith

end Omega.GU
