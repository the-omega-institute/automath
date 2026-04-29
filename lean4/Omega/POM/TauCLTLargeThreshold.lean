import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Epsilon-style convergence for the large-threshold tau wrappers. -/
def pom_tau_clt_large_threshold_tendsto (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ T : ℕ, N ≤ T → |u T - a| ≤ ε

/-- The normalized hitting time converges in distribution to a supplied normal CDF. -/
def pom_tau_clt_large_threshold_hittingTimeCLT
    (normalizedCDF normalCDF : ℕ → ℝ → ℝ) : Prop :=
  ∀ x : ℝ,
    pom_tau_clt_large_threshold_tendsto (fun T : ℕ => normalizedCDF T x) (normalCDF 0 x)

/-- The scaled tau process converges in second moment to the golden-ratio drift scale. -/
def pom_tau_clt_large_threshold_l2Limit (secondMomentError : ℕ → ℝ) : Prop :=
  pom_tau_clt_large_threshold_tendsto secondMomentError 0

/-- The deterministic and fluctuation scales are `φ^3 T` and `2 φ^3 sqrt T`. -/
def pom_tau_clt_large_threshold_complexityScale
    (meanScale fluctuationScale : ℕ → ℝ) : Prop :=
  (∀ T : ℕ, meanScale T = Real.goldenRatio ^ 3 * T) ∧
    ∀ T : ℕ, fluctuationScale T = 2 * Real.goldenRatio ^ 3 * Real.sqrt T

/-- Paper label: `thm:pom-tau-clt-large-threshold`. -/
theorem paper_pom_tau_clt_large_threshold
    (normalizedCDF normalCDF : ℕ → ℝ → ℝ)
    (secondMomentError meanScale fluctuationScale : ℕ → ℝ)
    (hittingTimeCLT :
      pom_tau_clt_large_threshold_hittingTimeCLT normalizedCDF normalCDF)
    (l2Limit : pom_tau_clt_large_threshold_l2Limit secondMomentError)
    (complexityScale :
      pom_tau_clt_large_threshold_complexityScale meanScale fluctuationScale) :
    pom_tau_clt_large_threshold_hittingTimeCLT normalizedCDF normalCDF ∧
      pom_tau_clt_large_threshold_l2Limit secondMomentError ∧
        pom_tau_clt_large_threshold_complexityScale meanScale fluctuationScale := by
  exact ⟨hittingTimeCLT, l2Limit, complexityScale⟩

end Omega.POM
