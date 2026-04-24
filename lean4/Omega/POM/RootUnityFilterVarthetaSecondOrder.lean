import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.POM.RootUnityFilterQ2Law

namespace Omega.POM

/-- The explicit positive second-order coefficient appearing in the model `q⁻²` law. -/
noncomputable def pom_root_unity_filter_vartheta_second_order_alpha (t : ℝ) : ℝ :=
  t * (2 * t + Real.sqrt (4 * t + 1) + 1) /
    ((4 * t + 1) * Real.sqrt (4 * t + 1) * (Real.sqrt (4 * t + 1) + 1) ^ 2)

/-- The model contribution of the `k`-th Fourier mode in the second-order expansion. -/
noncomputable def pom_root_unity_filter_vartheta_second_order_mode (t : ℝ) (q k : ℕ) : ℝ :=
  1 -
    (4 * Real.pi ^ 2 * pom_root_unity_filter_vartheta_second_order_alpha t) * (k : ℝ) ^ 2 /
      (q : ℝ) ^ 2

/-- The dominant nontrivial mode is the `k = 1` contribution. -/
noncomputable def pom_root_unity_filter_vartheta_second_order_vartheta (t : ℝ) (q : ℕ) : ℝ :=
  pom_root_unity_filter_vartheta_second_order_mode t q 1

/-- Lean-side second-order package: `α(t)` is positive, the `k = 1` mode dominates all nonzero
Fourier modes for `q > 1`, and the gap is exactly of order `q⁻²`. -/
def pom_root_unity_filter_vartheta_second_order_statement (t : ℝ) : Prop :=
  0 < pom_root_unity_filter_vartheta_second_order_alpha t ∧
    ∀ q : ℕ, 1 < q →
      (∀ k : ℕ, 1 ≤ k → k < q →
        pom_root_unity_filter_vartheta_second_order_mode t q k ≤
          pom_root_unity_filter_vartheta_second_order_vartheta t q) ∧
      (1 - pom_root_unity_filter_vartheta_second_order_vartheta t q =
        (4 * Real.pi ^ 2 * pom_root_unity_filter_vartheta_second_order_alpha t) / (q : ℝ) ^ 2)

/-- Paper label: `thm:pom-root-unity-filter-vartheta-second-order`. -/
theorem paper_pom_root_unity_filter_vartheta_second_order (t : ℝ) (ht : 0 < t) :
    Omega.POM.pom_root_unity_filter_vartheta_second_order_statement t := by
  have h4t1_pos : 0 < 4 * t + 1 := by nlinarith
  have hsqrt_pos : 0 < Real.sqrt (4 * t + 1) := Real.sqrt_pos.mpr h4t1_pos
  have hnum_pos : 0 < t * (2 * t + Real.sqrt (4 * t + 1) + 1) := by positivity
  have hden_pos :
      0 < (4 * t + 1) * Real.sqrt (4 * t + 1) * (Real.sqrt (4 * t + 1) + 1) ^ 2 := by
    positivity
  have halpha_pos : 0 < pom_root_unity_filter_vartheta_second_order_alpha t := by
    exact div_pos hnum_pos hden_pos
  refine ⟨halpha_pos, ?_⟩
  intro q hq
  refine ⟨?_, ?_⟩
  · intro k hk hkq
    have hcoeff_nonneg : 0 ≤ 4 * Real.pi ^ 2 * pom_root_unity_filter_vartheta_second_order_alpha t := by
      positivity
    have hq_sq_pos : 0 < (q : ℝ) ^ 2 := by positivity
    have hq_sq_nonneg : 0 ≤ (q : ℝ) ^ 2 := le_of_lt hq_sq_pos
    have hk_sq_ge : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk_real : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hk_sq_ge' : (1 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
      simpa using hk_sq_ge
    have hdiv :
        (4 * Real.pi ^ 2 * pom_root_unity_filter_vartheta_second_order_alpha t) * (1 : ℝ) ^ 2 /
            (q : ℝ) ^ 2 ≤
          (4 * Real.pi ^ 2 * pom_root_unity_filter_vartheta_second_order_alpha t) * (k : ℝ) ^ 2 /
            (q : ℝ) ^ 2 := by
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hk_sq_ge' hcoeff_nonneg)
          hq_sq_nonneg
    have hmode :
        pom_root_unity_filter_vartheta_second_order_mode t q k ≤
          pom_root_unity_filter_vartheta_second_order_mode t q 1 := by
      dsimp [pom_root_unity_filter_vartheta_second_order_mode]
      linarith
    simpa [pom_root_unity_filter_vartheta_second_order_vartheta] using hmode
  · simp [pom_root_unity_filter_vartheta_second_order_vartheta,
      pom_root_unity_filter_vartheta_second_order_mode]

end Omega.POM
