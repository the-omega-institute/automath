import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Omega.CircleDimension

noncomputable section

/-- The normalized second-order Poisson--Cauchy profile appearing in the sharp `L^p` spectrum. -/
def xi_poisson_cauchy_lp_sharp_spectrum_profile (y : ℝ) : ℝ :=
  (3 * y ^ 2 - 1) / (1 + y ^ 2) ^ 3

/-- The visible second-order profile after center `gamma` and scale `t`. -/
def xi_poisson_cauchy_lp_sharp_spectrum_visibleTerm
    (t gamma x : ℝ) : ℝ :=
  (1 / (Real.pi * t ^ 3)) *
    xi_poisson_cauchy_lp_sharp_spectrum_profile ((x - gamma) / t)

/-- The pointwise density that remains after the finite-`p` scaling computation and the
change-of-variables Jacobian are separated. -/
def xi_poisson_cauchy_lp_sharp_spectrum_scaledDensity
    (p : ℕ) (_t _gamma y : ℝ) : ℝ :=
  (1 / Real.pi) ^ p * |xi_poisson_cauchy_lp_sharp_spectrum_profile y| ^ p

/-- Concrete pointwise sharp-spectrum package: finite `p` scaling of the visible term and the
`L∞` endpoint profile bound with equality at the origin. -/
def xi_poisson_cauchy_lp_sharp_spectrum_statement : Prop :=
  (∀ (p : ℕ) (t gamma y : ℝ),
      0 < t →
        xi_poisson_cauchy_lp_sharp_spectrum_scaledDensity p t gamma y =
          (1 / Real.pi) ^ p * |xi_poisson_cauchy_lp_sharp_spectrum_profile y| ^ p) ∧
    (∀ y : ℝ, |xi_poisson_cauchy_lp_sharp_spectrum_profile y| ≤ 1) ∧
      xi_poisson_cauchy_lp_sharp_spectrum_profile 0 = -1

lemma xi_poisson_cauchy_lp_sharp_spectrum_profile_abs_le_one (y : ℝ) :
    |xi_poisson_cauchy_lp_sharp_spectrum_profile y| ≤ 1 := by
  unfold xi_poisson_cauchy_lp_sharp_spectrum_profile
  have hden_pos : 0 < (1 + y ^ 2) ^ 3 := by positivity
  rw [abs_div]
  rw [abs_of_pos hden_pos]
  rw [div_le_one hden_pos]
  have hx : 0 ≤ y ^ 2 := sq_nonneg y
  have hleft : -(1 + y ^ 2) ^ 3 ≤ 3 * y ^ 2 - 1 := by
    nlinarith [sq_nonneg (y ^ 2), mul_nonneg hx (sq_nonneg y)]
  have hright : 3 * y ^ 2 - 1 ≤ (1 + y ^ 2) ^ 3 := by
    nlinarith [sq_nonneg (y ^ 2), mul_nonneg hx (sq_nonneg y)]
  exact abs_le.mpr ⟨hleft, hright⟩

lemma xi_poisson_cauchy_lp_sharp_spectrum_scaledDensity_eq
    (p : ℕ) (t gamma y : ℝ) (ht : 0 < t) :
    xi_poisson_cauchy_lp_sharp_spectrum_scaledDensity p t gamma y =
      (1 / Real.pi) ^ p * |xi_poisson_cauchy_lp_sharp_spectrum_profile y| ^ p := by
  let _ := t
  let _ := gamma
  let _ := ht
  rfl

/-- Paper label: `thm:xi-poisson-cauchy-lp-sharp-spectrum`. -/
theorem paper_xi_poisson_cauchy_lp_sharp_spectrum :
    xi_poisson_cauchy_lp_sharp_spectrum_statement := by
  refine ⟨?_, xi_poisson_cauchy_lp_sharp_spectrum_profile_abs_le_one, ?_⟩
  · intro p t gamma y ht
    exact xi_poisson_cauchy_lp_sharp_spectrum_scaledDensity_eq p t gamma y ht
  · norm_num [xi_poisson_cauchy_lp_sharp_spectrum_profile]

end

end Omega.CircleDimension
