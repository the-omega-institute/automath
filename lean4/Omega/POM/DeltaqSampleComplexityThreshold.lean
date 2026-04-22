import Omega.POM.DeltaqQuadraticObservableMaxExponent
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for turning the quadratic-observable exponent bound into a sample-complexity
threshold for a relative mean-square target. The sequence `Q` models the single-sample quadratic
variance profile, `sampleCount` is the number of independent samples, and `accuracy` is the
admissible relative MSE budget. -/
structure PomDeltaqSampleComplexityThresholdData where
  Λ : ℝ
  r : ℝ
  Z1 : ℕ → ℝ
  Z2 : ℕ → ℝ
  Q : ℕ → ℝ
  sampleCount : ℕ → ℝ
  relativeMSE : ℕ → ℝ
  accuracy : ℕ → ℝ
  hΛ : 0 ≤ Λ
  hr : 0 < r
  hsampleCount_pos : ∀ m : ℕ, 0 < sampleCount m
  hZ1 : ∃ C > 0, ∀ m : ℕ, |Z1 m| ≤ C * Λ ^ m
  hZ2 : ∃ C > 0, ∀ m : ℕ, |Z2 m| ≤ C * Λ ^ m
  hQ : ∀ m : ℕ, Q m = Z1 m * Z2 m
  hrelativeMSE :
    ∀ m : ℕ, relativeMSE m = (|Q m| / r ^ m) / sampleCount m

namespace PomDeltaqSampleComplexityThresholdData

/-- If the allowed budget dominates the quadratic exponent profile divided by the sample count,
the relative mean-square error stays below that budget. -/
def sample_complexity_threshold (D : PomDeltaqSampleComplexityThresholdData) : Prop :=
  ∃ C > 0, ∀ m : ℕ,
    C * ((D.Λ ^ 2 / D.r) ^ m / D.sampleCount m) ≤ D.accuracy m →
      D.relativeMSE m ≤ D.accuracy m

end PomDeltaqSampleComplexityThresholdData

open PomDeltaqSampleComplexityThresholdData

/-- Paper label: `cor:pom-deltaq-sample-complexity-threshold`. The quadratic-observable exponent
bound controls the one-sample relative variance at scale `Λ² / r`; dividing by `N` via the
variance-of-the-sample-mean identity yields the required sample-complexity threshold. -/
theorem paper_pom_deltaq_sample_complexity_threshold
    (D : PomDeltaqSampleComplexityThresholdData) : D.sample_complexity_threshold := by
  rcases pom_deltaq_quadratic_observable_max_exponent_nonneg D.Λ D.r D.Z1 D.Z2 D.Q D.hΛ
      (le_of_lt D.hr) D.hZ1 D.hZ2 D.hQ with
    ⟨C, hCpos, hGrowth⟩
  refine ⟨C, hCpos, ?_⟩
  intro m hThreshold
  have hBound :
      D.relativeMSE m ≤ C * ((D.Λ ^ 2 / D.r) ^ m / D.sampleCount m) := by
    rw [D.hrelativeMSE m]
    calc
      (|D.Q m| / D.r ^ m) / D.sampleCount m ≤
          (C * (D.Λ ^ 2 / D.r) ^ m) / D.sampleCount m := by
        exact div_le_div_of_nonneg_right (hGrowth m) (le_of_lt (D.hsampleCount_pos m))
      _ = C * ((D.Λ ^ 2 / D.r) ^ m / D.sampleCount m) := by ring
  exact le_trans hBound hThreshold

end Omega.POM
