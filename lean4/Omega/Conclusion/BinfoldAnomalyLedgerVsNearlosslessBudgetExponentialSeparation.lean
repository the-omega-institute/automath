import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinMaxFiberExponent
import Omega.GU.FoldBinMinDegeneracyFibNonpersistent
import Omega.OperatorAlgebra.FoldGaugeGroupStructure
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

open Filter Topology
open scoped goldenRatio

namespace Omega.Conclusion

/-- Constant `d_min = 2` model on the Fibonacci syntax space `X_m`, used to read the
abelianization order as a pure `2`-power of exponent `|X_m| = F_{m+2}`. -/
def conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation_constant_two_fiber
    (m : ℕ) : Fin (Nat.fib (m + 2)) → ℕ :=
  fun _ => 2

/-- Paper label:
`thm:conclusion-binfold-anomaly-ledger-vs-nearlossless-budget-exponential-separation`.

For the constant `d_min = 2` anomaly-block model, the bin-fold gauge abelianization has
`F_{m+2}` binary generators. By contrast, the stronger near-lossless lower bound
`|X_m| · F_{m/2} ≤ 2^m` cannot hold uniformly, and the dyadic/ledger ratio has exponential
rate `log (2 / φ)`. -/
theorem paper_conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation :
    (∀ m : ℕ,
      Nat.log 2
          (Omega.OperatorAlgebra.foldGaugeAbelianizationOrder
            (conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation_constant_two_fiber
              m)) =
        Nat.fib (m + 2)) ∧
      ¬ (∀ m : ℕ, Nat.fib (m + 2) * Nat.fib (m / 2) ≤ 2 ^ m) ∧
      Tendsto (fun m : ℕ => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
        atTop (nhds (Real.log (2 / Real.goldenRatio))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    have hab :
        Omega.OperatorAlgebra.foldGaugeAbelianizationOrder
            (conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation_constant_two_fiber
              m) =
          2 ^ Nat.fib (m + 2) := by
      simpa
        [conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation_constant_two_fiber]
        using
          (Omega.Zeta.paper_xi_time_part65_binfold_gauge_center_abelianization_exact
            (m := Nat.fib (m + 2))
            (fiber :=
              conclusion_binfold_anomaly_ledger_vs_nearlossless_budget_exponential_separation_constant_two_fiber
                m)).2
    rw [hab]
    exact Nat.log_pow (by decide) (Nat.fib (m + 2))
  · intro hbudget
    have hnonpersistent :=
      Omega.GU.paper_fold_bin_min_degeneracy_fib_nonpersistent
        (dmin := fun m => Nat.fib (m / 2))
        (Xcard := fun m => Nat.fib (m + 2))
        (totalMass := fun m => 2 ^ m)
        (hXcard := by intro m; rfl)
        (hlower := by intro m; simpa using hbudget m)
        (htotal := by intro m; rfl)
    apply hnonpersistent
    intro N
    refine ⟨2 * N, by omega, even_two_mul N, rfl⟩
  · simpa using Omega.paper_fold_bin_max_fiber_exponent.2

end Omega.Conclusion
