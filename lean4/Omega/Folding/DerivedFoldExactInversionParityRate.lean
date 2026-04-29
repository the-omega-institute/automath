import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Omega.Folding.DerivedFoldExactInversionDyadicThreshold
import Omega.Folding.Entropy
import Omega.POM.MaxAtomicWeightParitySecondOrder

open Filter
open scoped goldenRatio

namespace Omega.Folding

/-- The critical exact-inversion bitrate extracted from the Fibonacci growth exponent. -/
noncomputable def derived_fold_exact_inversion_parity_rate_critical_rate : ℝ :=
  Real.log Real.goldenRatio / Real.log 2

/-- Paper label: `cor:derived-fold-exact-inversion-parity-rate`. The audited dyadic-threshold
formula splits into even and odd Fibonacci branches, the even branch has the exact Binet closed
form and asymptotic rate `log φ`, and any rate below/above the critical binary slope is
eventually subcritical/supercritical in the corresponding logarithmic comparison. -/
theorem paper_derived_fold_exact_inversion_parity_rate :
    (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      derivedFoldDyadicExactInversionThreshold (2 * k) = Nat.clog 2 (Nat.fib (k + 2))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      derivedFoldDyadicExactInversionThreshold (2 * k + 1) = Nat.clog 2 (2 * Nat.fib (k + 1))) ∧
    (∀ k : ℕ, (Nat.fib (k + 2) : ℝ) = (φ ^ (k + 2) - ψ ^ (k + 2)) / Real.sqrt 5) ∧
    Tendsto (fun m : ℕ => Real.log (Nat.fib (m + 2) : ℝ) / (m : ℝ))
      atTop (nhds (Real.log Real.goldenRatio)) ∧
    (∀ β : ℝ, β < derived_fold_exact_inversion_parity_rate_critical_rate →
      ∀ᶠ m : ℕ in atTop, β * Real.log 2 < Real.log (Nat.fib (m + 2) : ℝ) / (m : ℝ)) ∧
    (∀ β : ℝ, derived_fold_exact_inversion_parity_rate_critical_rate < β →
      ∀ᶠ m : ℕ in atTop, Real.log (Nat.fib (m + 2) : ℝ) / (m : ℝ) < β * Real.log 2) := by
  have hdyadic := paper_derived_fold_exact_inversion_dyadic_threshold
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  refine ⟨hdyadic.1, hdyadic.2, ?_, Omega.Entropy.topological_entropy_eq_log_phi, ?_, ?_⟩
  · intro k
    have hparity := Omega.POM.paper_pom_max_atomic_weight_parity_second_order
    simpa [Omega.POM.pMaxEvenBranch] using hparity.1 k
  · intro β hβ
    have htarget : β * Real.log 2 < Real.log Real.goldenRatio := by
      unfold derived_fold_exact_inversion_parity_rate_critical_rate at hβ
      have hmul :
          β * Real.log 2 <
            (Real.log Real.goldenRatio / Real.log 2) * Real.log 2 :=
        mul_lt_mul_of_pos_right hβ hlog2_pos
      have hcancel :
          (Real.log Real.goldenRatio / Real.log 2) * Real.log 2 = Real.log Real.goldenRatio := by
        field_simp [hlog2_pos.ne']
      simpa [hcancel] using hmul
    exact Omega.Entropy.topological_entropy_eq_log_phi.eventually (Ioi_mem_nhds htarget)
  · intro β hβ
    have htarget : Real.log Real.goldenRatio < β * Real.log 2 := by
      unfold derived_fold_exact_inversion_parity_rate_critical_rate at hβ
      have hmul : (Real.log Real.goldenRatio / Real.log 2) * Real.log 2 < β * Real.log 2 :=
        mul_lt_mul_of_pos_right hβ hlog2_pos
      have hcancel :
          (Real.log Real.goldenRatio / Real.log 2) * Real.log 2 = Real.log Real.goldenRatio := by
        field_simp [hlog2_pos.ne']
      simpa [hcancel, mul_comm] using hmul
    exact Omega.Entropy.topological_entropy_eq_log_phi.eventually (Iio_mem_nhds htarget)

end Omega.Folding
