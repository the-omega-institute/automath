import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The scaled-shifted Cayley modulus square from the chapter-local real wrapper. -/
noncomputable def xiScaledShiftedCayleyModSq (a δ γ x₀ : ℝ) : ℝ :=
  ((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2)

/-- The corresponding depth `1 - |w|²`. -/
noncomputable def xiScaledShiftedCayleyDepth (a δ γ x₀ : ℝ) : ℝ :=
  1 - xiScaledShiftedCayleyModSq a δ γ x₀

/-- The optimal scale `a* = sqrt((γ - x₀)^2 + δ^2)`. -/
noncomputable def xiScaledShiftedOptimalScale (δ γ x₀ : ℝ) : ℝ :=
  Real.sqrt ((γ - x₀) ^ 2 + δ ^ 2)

/-- The corresponding maximal depth. -/
noncomputable def xiScaledShiftedOptimalDepth (δ γ x₀ : ℝ) : ℝ :=
  2 * δ / (δ + xiScaledShiftedOptimalScale δ γ x₀)

theorem xiScaledShiftedCayley_denom_pos (a δ γ x₀ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    0 < (γ - x₀) ^ 2 + (δ + a) ^ 2 := by
  have hsq : 0 ≤ (γ - x₀) ^ 2 := sq_nonneg _
  have hshift : 0 < δ + a := by linarith
  have hshift_sq : 0 < (δ + a) ^ 2 := sq_pos_of_pos hshift
  linarith

theorem xiScaledShiftedCayleyDepth_formula (a δ γ x₀ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    xiScaledShiftedCayleyDepth a δ γ x₀ =
      4 * a * δ / ((γ - x₀) ^ 2 + (δ + a) ^ 2) := by
  unfold xiScaledShiftedCayleyDepth xiScaledShiftedCayleyModSq
  have hden :
      ((γ - x₀) ^ 2 + (δ + a) ^ 2) ≠ 0 :=
    ne_of_gt (xiScaledShiftedCayley_denom_pos a δ γ x₀ ha hδ)
  field_simp [hden]
  ring

theorem xiScaledShiftedOptimalScale_sq (δ γ x₀ : ℝ) :
    xiScaledShiftedOptimalScale δ γ x₀ ^ 2 = (γ - x₀) ^ 2 + δ ^ 2 := by
  unfold xiScaledShiftedOptimalScale
  rw [Real.sq_sqrt]
  positivity

theorem xiScaledShiftedOptimalScale_pos (δ γ x₀ : ℝ) (hδ : 0 < δ) :
    0 < xiScaledShiftedOptimalScale δ γ x₀ := by
  unfold xiScaledShiftedOptimalScale
  apply Real.sqrt_pos.2
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  nlinarith

/-- The scaled-shifted Cayley depth admits the explicit modulus/depth formulas, the optimal
scale `a*`, the closed-form maximum, and `a*` is the unique maximizer on `a > 0`.
    thm:xi-scaled-shifted-cayley-depth-optimal-scale -/
def XiScaledShiftedCayleyDepthOptimalScaleStatement : Prop :=
  ∀ {δ γ x₀ : ℝ}, 0 < δ →
    (∀ {a : ℝ}, 0 < a →
      xiScaledShiftedCayleyModSq a δ γ x₀ =
        ((γ - x₀) ^ 2 + (δ - a) ^ 2) / ((γ - x₀) ^ 2 + (δ + a) ^ 2) ∧
      xiScaledShiftedCayleyDepth a δ γ x₀ =
        4 * a * δ / ((γ - x₀) ^ 2 + (δ + a) ^ 2)) ∧
    xiScaledShiftedCayleyDepth (xiScaledShiftedOptimalScale δ γ x₀) δ γ x₀ =
      xiScaledShiftedOptimalDepth δ γ x₀ ∧
    (∀ {a : ℝ}, 0 < a →
      xiScaledShiftedCayleyDepth a δ γ x₀ ≤ xiScaledShiftedOptimalDepth δ γ x₀) ∧
    (∀ {a : ℝ}, 0 < a →
      xiScaledShiftedCayleyDepth a δ γ x₀ = xiScaledShiftedOptimalDepth δ γ x₀ →
        a = xiScaledShiftedOptimalScale δ γ x₀)

theorem paper_xi_scaled_shifted_cayley_depth_optimal_scale :
    XiScaledShiftedCayleyDepthOptimalScaleStatement := by
  intro δ γ x₀ hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨rfl, xiScaledShiftedCayleyDepth_formula a δ γ x₀ ha hδ⟩
  · let s := xiScaledShiftedOptimalScale δ γ x₀
    have hs_pos : 0 < s := xiScaledShiftedOptimalScale_pos δ γ x₀ hδ
    have hs_sq : s ^ 2 = (γ - x₀) ^ 2 + δ ^ 2 := xiScaledShiftedOptimalScale_sq δ γ x₀
    have hδs_pos : 0 < δ + s := by positivity
    rw [xiScaledShiftedCayleyDepth_formula s δ γ x₀ hs_pos hδ]
    unfold xiScaledShiftedOptimalDepth
    have hden :
        (γ - x₀) ^ 2 + (δ + s) ^ 2 = 2 * s * (δ + s) := by
      nlinarith [hs_sq]
    rw [hden]
    calc
      4 * s * δ / (2 * s * (δ + s)) = 4 * δ / (2 * (δ + s)) := by
        field_simp [ne_of_gt hs_pos]
      _ = 2 * δ / (δ + s) := by
        field_simp [ne_of_gt hδs_pos]
        ring
  · intro a ha
    let s := xiScaledShiftedOptimalScale δ γ x₀
    have hs_sq : s ^ 2 = (γ - x₀) ^ 2 + δ ^ 2 := xiScaledShiftedOptimalScale_sq δ γ x₀
    have hs_pos : 0 < s := xiScaledShiftedOptimalScale_pos δ γ x₀ hδ
    have hden_pos : 0 < (γ - x₀) ^ 2 + (δ + a) ^ 2 :=
      xiScaledShiftedCayley_denom_pos a δ γ x₀ ha hδ
    have hδs_pos : 0 < δ + s := by positivity
    rw [xiScaledShiftedCayleyDepth_formula a δ γ x₀ ha hδ]
    unfold xiScaledShiftedOptimalDepth
    apply (div_le_div_iff₀ hden_pos hδs_pos).2
    nlinarith [sq_nonneg (a - s), hs_sq]
  · intro a ha heq
    let s := xiScaledShiftedOptimalScale δ γ x₀
    have hs_sq : s ^ 2 = (γ - x₀) ^ 2 + δ ^ 2 := xiScaledShiftedOptimalScale_sq δ γ x₀
    have hs_pos : 0 < s := xiScaledShiftedOptimalScale_pos δ γ x₀ hδ
    have hden_pos : 0 < (γ - x₀) ^ 2 + (δ + a) ^ 2 :=
      xiScaledShiftedCayley_denom_pos a δ γ x₀ ha hδ
    have hδs_pos : 0 < δ + s := by positivity
    rw [xiScaledShiftedCayleyDepth_formula a δ γ x₀ ha hδ] at heq
    unfold xiScaledShiftedOptimalDepth at heq
    have hden_ne : ((γ - x₀) ^ 2 + (δ + a) ^ 2) ≠ 0 := ne_of_gt hden_pos
    have hδs_ne : δ + s ≠ 0 := ne_of_gt hδs_pos
    have hcross : 4 * a * (δ + s) = 2 * ((γ - x₀) ^ 2 + (δ + a) ^ 2) := by
      have h :
          4 * a = 2 * ((γ - x₀) ^ 2 + (δ + a) ^ 2) / (δ + s) := by
        have h' := heq
        field_simp [hden_ne, hδs_ne] at h'
        simpa [mul_comm, mul_left_comm, mul_assoc, two_mul, add_comm, add_left_comm, add_assoc]
          using h'
      exact (eq_div_iff hδs_ne).mp h
    have hsq_zero : (a - s) ^ 2 = 0 := by
      nlinarith [hcross, hs_sq]
    have hs_eq : a - s = 0 := sq_eq_zero_iff.mp hsq_zero
    linarith

end Omega.Zeta
