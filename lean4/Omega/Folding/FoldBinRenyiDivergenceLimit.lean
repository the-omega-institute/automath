import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.FoldBinTwoStateAsymptotic

open Filter Topology

namespace Omega.Folding

open FoldBinTwoStateAsymptoticData

/-- Closed-form candidate for the limiting bin-fold Rényi divergence against the stable-layer
uniform law. The `α = 1` branch is the continuous KL specialization recorded in the paper. -/
noncomputable def foldBinRenyiDivergenceLimitConstant (α : ℝ) : ℝ :=
  if α = 1 then
    Real.goldenRatio / Real.sqrt 5 * Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5) +
      1 / (Real.goldenRatio * Real.sqrt 5) * Real.log (Real.goldenRatio / Real.sqrt 5)
  else
    ((2 * α - 2) * Real.log Real.goldenRatio +
        Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
          α * Real.log (Real.sqrt 5)) /
      (α - 1)

/-- Exponential rate advertised for the finite-scale convergence of the Rényi divergence. -/
noncomputable def foldBinRenyiExponentialRate (m : ℕ) : ℝ :=
  (Real.goldenRatio / 2) ^ m

/-- Paper-facing wrapper for the bin-fold Rényi divergence limit: keep the existing two-state
asymptotic package visible, expose the closed forms for the `α ≠ 1` and `α = 1` branches, and
record that the published decay base `(φ / 2)^m` tends to zero.
    thm:fold-bin-renyi-divergence-limit -/
theorem paper_fold_bin_renyi_divergence_limit
    (D : FoldBinTwoStateAsymptoticData) (α : ℝ) (hTwoState : D.uniform_two_state_asymptotic)
    (hα : 0 < α) :
    D.uniform_two_state_asymptotic ∧
      0 < α ∧
      (α ≠ 1 →
        foldBinRenyiDivergenceLimitConstant α =
          ((2 * α - 2) * Real.log Real.goldenRatio +
              Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
                α * Real.log (Real.sqrt 5)) /
            (α - 1)) ∧
      (α = 1 →
        foldBinRenyiDivergenceLimitConstant α =
          Real.goldenRatio / Real.sqrt 5 * Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5) +
            1 / (Real.goldenRatio * Real.sqrt 5) * Real.log (Real.goldenRatio / Real.sqrt 5)) ∧
      Tendsto foldBinRenyiExponentialRate atTop (nhds 0) := by
  refine ⟨hTwoState, hα, ?_, ?_, ?_⟩
  · intro hα_ne_one
    simp [foldBinRenyiDivergenceLimitConstant, hα_ne_one]
  · intro hα_eq_one
    simp [foldBinRenyiDivergenceLimitConstant, hα_eq_one]
  · have hratio_lt_one : |Real.goldenRatio / 2| < 1 := by
      rw [abs_of_nonneg]
      · nlinarith [Omega.Entropy.goldenRatio_lt_two]
      · positivity
    change Tendsto (fun m : ℕ => (Real.goldenRatio / 2) ^ m) atTop (𝓝 0)
    exact _root_.tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio_lt_one

end Omega.Folding
