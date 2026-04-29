import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiScaledShiftedCayleyDepthOptimalScale

namespace Omega.Zeta

/-- The admissible upper branch from the scaled-shifted Jensen quadratic. -/
noncomputable def xiScaledShiftedDeltaUpperBound (a r t : ℝ) : ℝ :=
  (a * (1 + r ^ 2) - Real.sqrt (4 * a ^ 2 * r ^ 2 - t ^ 2 * (1 - r ^ 2) ^ 2)) / (1 - r ^ 2)

/-- A concrete Jensen-style consequence: the exclusion radius inequality rewrites to the quadratic
constraint in `δ`; if the height gap satisfies `t ≤ 2 a r / (1 - r²)`, then the discriminant is
nonnegative; and in the comoving specialization `t = 0`, the displayed upper branch collapses to
`a (1 - r) / (1 + r)`.
    thm:xi-scaled-shifted-jensen-implies-delta-bound -/
def XiScaledShiftedJensenImpliesDeltaBoundStatement : Prop :=
  ∀ {a δ γ x₀ r : ℝ},
    0 < a →
    0 < δ →
    0 ≤ r →
    r < 1 →
    r ^ 2 ≤ xiScaledShiftedCayleyModSq a δ γ x₀ →
    let t := |γ - x₀|
    ((1 - r ^ 2) * δ ^ 2 - 2 * a * (1 + r ^ 2) * δ + (1 - r ^ 2) * (t ^ 2 + a ^ 2) ≥ 0) ∧
    (t ≤ 2 * a * r / (1 - r ^ 2) →
      0 ≤ 4 * a ^ 2 * r ^ 2 - t ^ 2 * (1 - r ^ 2) ^ 2) ∧
    xiScaledShiftedDeltaUpperBound a r 0 = a * (1 - r) / (1 + r)

theorem paper_xi_scaled_shifted_jensen_implies_delta_bound :
    XiScaledShiftedJensenImpliesDeltaBoundStatement := by
  intro a δ γ x₀ r ha hδ hr hrlt hmod
  let t : ℝ := |γ - x₀|
  have hprev := paper_xi_scaled_shifted_cayley_depth_optimal_scale (δ := δ) (γ := γ) (x₀ := x₀) hδ
  have hmod_formula :
      xiScaledShiftedCayleyModSq a δ γ x₀ =
        ((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2) :=
    (hprev.1 ha).1
  have hmod_denom_pos : 0 < (γ - x₀) ^ 2 + (δ + a) ^ 2 :=
    xiScaledShiftedCayley_denom_pos a δ γ x₀ ha hδ
  have hquad_raw : r ^ 2 * ((γ - x₀) ^ 2 + (δ + a) ^ 2) ≤ (γ - x₀) ^ 2 + (δ - a) ^ 2 := by
    have hmod' :
        r ^ 2 ≤
          (((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2)) := by
      simpa [hmod_formula] using hmod
    have hmul :
        r ^ 2 * ((γ - x₀) ^ 2 + (δ + a) ^ 2) ≤
          (((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2)) *
            ((γ - x₀) ^ 2 + (δ + a) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hmod' (le_of_lt hmod_denom_pos)
    have hcancel :
        (((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2)) *
            ((γ - x₀) ^ 2 + (δ + a) ^ 2) =
          (γ - x₀) ^ 2 + (δ - a) ^ 2 := by
      field_simp [ne_of_gt hmod_denom_pos]
    simpa [hcancel] using hmul
  have ht_sq : t ^ 2 = (γ - x₀) ^ 2 := by
    dsimp [t]
    rw [sq_abs]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [t]
    nlinarith [hquad_raw]
  · intro htbound
    have htbound' : |γ - x₀| ≤ 2 * a * r / (1 - r ^ 2) := by
      simpa [t] using htbound
    have hden_pos : 0 < 1 - r ^ 2 := by
      nlinarith [sq_nonneg r, hr, hrlt]
    have hmul : |γ - x₀| * (1 - r ^ 2) ≤ 2 * a * r := by
      exact (le_div_iff₀ hden_pos).mp htbound'
    have hmul_nonneg : 0 ≤ |γ - x₀| * (1 - r ^ 2) := by
      positivity
    have hsq' :
        (|γ - x₀| * (1 - r ^ 2)) * (|γ - x₀| * (1 - r ^ 2)) ≤ (2 * a * r) * (2 * a * r) := by
      exact mul_self_le_mul_self hmul_nonneg hmul
    have hsq : |γ - x₀| ^ 2 * (1 - r ^ 2) ^ 2 ≤ 4 * a ^ 2 * r ^ 2 := by
      nlinarith
    nlinarith
  · have hden_pos : 0 < 1 - r ^ 2 := by
      nlinarith [sq_nonneg r, hr, hrlt]
    have hden_ne : (1 - r ^ 2) ≠ 0 := ne_of_gt hden_pos
    have hone : (1 + r) ≠ 0 := by positivity
    have hsqrt_zero : Real.sqrt (4 * a ^ 2 * r ^ 2) = 2 * a * r := by
      rw [show 4 * a ^ 2 * r ^ 2 = (2 * a * r) ^ 2 by ring, Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg (by positivity)
    unfold xiScaledShiftedDeltaUpperBound
    simp [hsqrt_zero]
    field_simp [hden_ne, hone]
    ring

end Omega.Zeta
