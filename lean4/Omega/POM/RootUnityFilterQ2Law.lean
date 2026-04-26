import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.FiberRewriteRootUnityFilterModqExpUniformization

namespace Omega.POM

/-- The explicit `q²` threshold obtained by solving the exponential contraction bound for a fixed
accuracy target. -/
noncomputable def pom_root_unity_filter_q2_law_threshold
    (S : FiberRewriteRootUnityFilterSystem) (α K ε : ℝ) : ℝ :=
  ((S.modulus : ℝ) ^ 2 / (4 * Real.pi ^ 2 * α)) * Real.log (K / ε)

/-- Paper label: `cor:pom-root-unity-filter-q2-law`. The existing root-of-unity-filter
uniformization package supplies the modulus positivity and strict contraction window. Solving the
model exponential decay inequality for the visible support size gives the expected `q²` threshold
law. -/
theorem paper_pom_root_unity_filter_q2_law
    (S : FiberRewriteRootUnityFilterSystem) {α K ε n : ℝ}
    (hα : 0 < α) (hK : 0 < K) (hε : 0 < ε)
    (hn : pom_root_unity_filter_q2_law_threshold S α K ε ≤ n) :
    rootUnityFilterProbabilityFormula S ∧
      rootUnityFilterExponentialUniformization S ∧
      K * Real.exp (-(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n)) ≤ ε := by
  have hunif := paper_pom_fiber_rewrite_root_of_unity_filter_modq_exp_uniformization S
  have hq_nat : 0 < S.modulus := lt_of_lt_of_le Nat.zero_lt_one S.modulus_pos
  have hq : 0 < (S.modulus : ℝ) := Nat.cast_pos.mpr hq_nat
  have hq_sq : 0 < (S.modulus : ℝ) ^ 2 := by positivity
  have hden_ne : 4 * Real.pi ^ 2 * α ≠ 0 := by positivity
  have hq_sq_ne : (S.modulus : ℝ) ^ 2 ≠ 0 := ne_of_gt hq_sq
  have hrate_pos : 0 < (4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2 := by positivity
  have hlog_le :
      Real.log (K / ε) ≤ ((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n := by
    have hmul := mul_le_mul_of_nonneg_left hn (le_of_lt hrate_pos)
    have hrewrite :
        ((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) *
            pom_root_unity_filter_q2_law_threshold S α K ε =
          Real.log (K / ε) := by
      unfold pom_root_unity_filter_q2_law_threshold
      field_simp [hden_ne, hq_sq_ne]
    rw [hrewrite] at hmul
    exact hmul
  have hexp :
      Real.exp (-(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n)) ≤ ε / K := by
    have hneg :
        -(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n) ≤ -Real.log (K / ε) := by
      linarith
    calc
      Real.exp (-(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n)) ≤
          Real.exp (-Real.log (K / ε)) := Real.exp_le_exp.mpr hneg
      _ = ε / K := by
        rw [Real.exp_neg, Real.exp_log]
        field_simp [hK.ne', hε.ne']
        positivity
  have hmulK :
      K * Real.exp (-(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n)) ≤ K * (ε / K) := by
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt hK)
  refine ⟨hunif.1, hunif.2, ?_⟩
  calc
    K * Real.exp (-(((4 * Real.pi ^ 2 * α) / (S.modulus : ℝ) ^ 2) * n)) ≤ K * (ε / K) := hmulK
    _ = ε := by field_simp [hK.ne']

end Omega.POM
