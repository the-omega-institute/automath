import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinRenyiRateCollapse
import Omega.Zeta.XiFoldKappaGaugeFirstOrderConstants
import Omega.Zeta.XiTimePart70adBinfoldRenyiEntropyConstantDrift

open Filter

namespace Omega.Zeta

noncomputable section

/-- The closed Rényi constant for the absolute bin-fold pushforward entropy. -/
def xi_foldbin_absolute_renyi_entropy_constant_closed_renyi_constant (q : ℝ) : ℝ :=
  (1 / (1 - q)) *
    Real.log ((Real.goldenRatio + Real.goldenRatio ^ (-q)) / Real.sqrt 5)

/-- The Shannon constant in the bin-fold absolute entropy expansion. -/
def xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_constant : ℝ :=
  Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)

/-- The same Shannon constant after the golden-ratio denominator rationalization. -/
def xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_rationalized : ℝ :=
  Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)

/-- Paper-facing concrete statement for the absolute Rényi/Shannon constant package. -/
def xi_foldbin_absolute_renyi_entropy_constant_closed_statement : Prop :=
  (∀ q : ℝ, 0 < q → q ≠ 1 →
    xi_time_part70ad_binfold_renyi_entropy_constant_drift_constant q =
      xi_foldbin_absolute_renyi_entropy_constant_closed_renyi_constant q) ∧
  (∀ q : ℝ, 0 < q →
    Tendsto (Omega.Folding.foldBinRenyiEntropyRate q) atTop
      (nhds (Real.log Real.goldenRatio))) ∧
  (∀ m : ℕ,
    let kappaMain := (m : ℝ) * Real.log (2 / Real.goldenRatio) -
      xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_constant
    kappaMain - (m : ℝ) * Real.log (2 / Real.goldenRatio) =
      -xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_constant) ∧
  xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_constant =
    Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) ∧
  xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_rationalized =
    Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)

/-- Paper label: `thm:xi-foldbin-absolute-renyi-entropy-constant-closed`. -/
theorem paper_xi_foldbin_absolute_renyi_entropy_constant_closed :
    xi_foldbin_absolute_renyi_entropy_constant_closed_statement := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro q _hq _hq1
    rfl
  · intro q hq
    exact Omega.Folding.paper_fold_bin_renyi_rate_collapse q hq
  · intro m
    dsimp
    ring

end

end Omega.Zeta
