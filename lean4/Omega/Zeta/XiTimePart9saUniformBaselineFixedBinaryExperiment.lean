import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoPointLimitLaw
import Omega.Zeta.XiFoldLastbitStatisticalSufficiencyCollapse

open scoped goldenRatio

namespace Omega.Zeta

open Omega.Folding

/-- Concrete seed for the already verified bin-fold two-point law. -/
def xiTimePart9saUniformBaselineSeed : FoldBinTwoStateAsymptoticData := {}

/-- Concrete xi-facing package for the fixed binary experiment: the exact Fibonacci last-bit
counts and limiting two-point masses come from the bin-fold package, while the Le Cam comparison
is represented by the existing last-bit sufficiency collapse instantiated with zero reconstruction
error. -/
def xiTimePart9saUniformBaselineFixedBinaryExperimentStatement : Prop :=
  paper_fold_bin_two_point_limit_law_statement xiTimePart9saUniformBaselineSeed ∧
    ∀ m : ℕ,
      xiFoldLastbitStatisticalSufficiency
        (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
        (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
        (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
        0 0 Real.goldenRatio m

/-- The fixed binary experiment is supplied by the existing two-point limit law together with the
zero-error instance of the xi last-bit Le Cam collapse. -/
theorem paper_xi_time_part9sa_uniform_baseline_fixed_binary_experiment_true :
    xiTimePart9saUniformBaselineFixedBinaryExperimentStatement := by
  refine ⟨paper_fold_bin_two_point_limit_law xiTimePart9saUniformBaselineSeed, ?_⟩
  intro m
  simpa using
    paper_xi_fold_lastbit_statistical_sufficiency_collapse
      (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
      (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
      (foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true)
      0 0 Real.goldenRatio m
      (by simp) (by simp) (by simp)

/-- Paper-facing wrapper for the fixed binary experiment attached to the uniform baseline.
    thm:xi-time-part9sa-uniform-baseline-fixed-binary-experiment -/
def paper_xi_time_part9sa_uniform_baseline_fixed_binary_experiment : Prop := by
  exact xiTimePart9saUniformBaselineFixedBinaryExperimentStatement

end Omega.Zeta
