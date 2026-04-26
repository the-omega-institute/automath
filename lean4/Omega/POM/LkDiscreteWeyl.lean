import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The inverse angle variable `θ(μ) = arccos(1 - μ / 2)` used in the discrete Weyl counting
formula. -/
def pom_lk_discrete_weyl_theta (μ : ℝ) : ℝ :=
  Real.arccos (1 - μ / 2)

/-- The linear Weyl main term attached to the half-odd-angle grid of `L_k`. -/
def pom_lk_discrete_weyl_main (k : ℕ) (μ : ℝ) : ℝ :=
  ((2 * k + 1 : ℝ) / (2 * Real.pi)) * pom_lk_discrete_weyl_theta μ

/-- The explicit inverse-count appearing in the discrete Weyl law. -/
def pom_lk_discrete_weyl_count (k : ℕ) (μ : ℝ) : ℕ :=
  Nat.floor (pom_lk_discrete_weyl_main k μ + 1 / 2)

/-- Paper label: `cor:pom-Lk-discrete-weyl`. The half-odd-angle inverse count is the floor of the
linearized angle variable, with the expected uniform `O(1)` floor error and the correct
`θ(μ) ∈ (0, π)` range for `μ ∈ (0, 4)`. -/
theorem paper_pom_lk_discrete_weyl :
    ∀ k : ℕ, ∀ {μ : ℝ}, 0 < μ → μ < 4 →
      pom_lk_discrete_weyl_count k μ =
          Nat.floor (pom_lk_discrete_weyl_main k μ + 1 / 2) ∧
        |((pom_lk_discrete_weyl_count k μ : ℝ) - pom_lk_discrete_weyl_main k μ)| ≤ 1 ∧
        0 < pom_lk_discrete_weyl_theta μ ∧ pom_lk_discrete_weyl_theta μ < Real.pi := by
  intro k μ hμ0 hμ4
  have harg_lt_one : 1 - μ / 2 < 1 := by nlinarith
  have harg_gt_neg_one : -1 < 1 - μ / 2 := by nlinarith
  have htheta_pos : 0 < pom_lk_discrete_weyl_theta μ := by
    unfold pom_lk_discrete_weyl_theta
    exact Real.arccos_pos.mpr harg_lt_one
  have htheta_lt_pi : pom_lk_discrete_weyl_theta μ < Real.pi := by
    unfold pom_lk_discrete_weyl_theta
    exact Real.arccos_lt_pi.mpr harg_gt_neg_one
  have htheta_nonneg : 0 ≤ pom_lk_discrete_weyl_theta μ := le_of_lt htheta_pos
  have hcoeff_nonneg : 0 ≤ ((2 * k + 1 : ℝ) / (2 * Real.pi)) := by positivity
  have hmain_nonneg : 0 ≤ pom_lk_discrete_weyl_main k μ := by
    exact mul_nonneg hcoeff_nonneg htheta_nonneg
  have hshift_nonneg : 0 ≤ pom_lk_discrete_weyl_main k μ + 1 / 2 := by linarith
  have hfloor_le :
      ((pom_lk_discrete_weyl_count k μ : ℕ) : ℝ) ≤ pom_lk_discrete_weyl_main k μ + 1 / 2 := by
    simpa [pom_lk_discrete_weyl_count] using
      (Nat.floor_le hshift_nonneg : ((Nat.floor (pom_lk_discrete_weyl_main k μ + 1 / 2) : ℕ) : ℝ) ≤
        pom_lk_discrete_weyl_main k μ + 1 / 2)
  have hlt_floor :
      pom_lk_discrete_weyl_main k μ + 1 / 2 <
        ((pom_lk_discrete_weyl_count k μ : ℕ) : ℝ) + 1 := by
    simpa [pom_lk_discrete_weyl_count] using
      (Nat.lt_floor_add_one (pom_lk_discrete_weyl_main k μ + 1 / 2) :
        pom_lk_discrete_weyl_main k μ + 1 / 2 <
          ((Nat.floor (pom_lk_discrete_weyl_main k μ + 1 / 2) : ℕ) : ℝ) + 1)
  have hdist_upper :
      ((pom_lk_discrete_weyl_count k μ : ℕ) : ℝ) - pom_lk_discrete_weyl_main k μ ≤ 1 / 2 := by
    nlinarith
  have hdist_lower :
      -((1 : ℝ) / 2) ≤
        ((pom_lk_discrete_weyl_count k μ : ℕ) : ℝ) - pom_lk_discrete_weyl_main k μ := by
    nlinarith
  have hdist_half :
      |((pom_lk_discrete_weyl_count k μ : ℕ) : ℝ) - pom_lk_discrete_weyl_main k μ| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨hdist_lower, hdist_upper⟩
  refine ⟨rfl, ?_, htheta_pos, htheta_lt_pi⟩
  linarith

end

end Omega.POM
