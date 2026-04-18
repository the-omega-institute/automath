import Mathlib.Tactic
import Omega.Folding.MetallicParetoScaleLaw

namespace Omega.Folding

/-- Sample-size specialization of the metallic Pareto scale law at `β(N) = log N / N`.
    cor:metallic-sample-threshold -/
theorem paper_metallic_sample_threshold (h : MetallicParetoScaleLawData) (N : Nat) (hN : 4 <= N)
    (hbeta : Real.log (N : Real) / (N : Real) < h.betaCritical) :
    1 <= h.optimalScale (Real.log (N : Real) / (N : Real)) ∧
      h.optimalScale (Real.log (N : Real) / (N : Real)) <= 3 / 2 ∧
      h.firstOrderBalance (Real.log (N : Real) / (N : Real)) := by
  rcases paper_metallic_pareto_scale_law h with ⟨hWindow, hBelow, _⟩
  have hN_real : (4 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by
    linarith
  have hN_one : (1 : ℝ) ≤ (N : ℝ) := by
    linarith
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_one
  have hbeta_nonneg : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := by
    exact div_nonneg hlog_nonneg hN_nonneg
  have hWindow' := hWindow (Real.log (N : ℝ) / (N : ℝ)) hbeta_nonneg
  exact ⟨hWindow'.1, hWindow'.2, hBelow (Real.log (N : ℝ) / (N : ℝ)) hbeta_nonneg hbeta⟩

end Omega.Folding
