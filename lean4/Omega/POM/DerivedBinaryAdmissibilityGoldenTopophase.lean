import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit
import Omega.Folding.FoldBinMaxFiberExponent

open Filter Topology
open scoped goldenRatio

namespace Omega.POM

/-- Paper label: `thm:derived-binary-admissibility-golden-topophase`. The binary-admissible
Fibonacci state count forces the golden endpoint rate `log (2 / φ)`, and the noncontractible
sector rewrites to the unique mod-`6` topophase decomposition. -/
theorem paper_derived_binary_admissibility_golden_topophase :
    Tendsto (fun m : ℕ => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
        atTop (nhds (Real.log (2 / Real.goldenRatio))) ∧
      ∀ m : ℕ,
        17 ≤ m →
          Omega.Conclusion.noncontractibleFiberCount m =
            if m % 6 = 0 ∨ m % 6 = 4 then Omega.Conclusion.noncontractibleMainFiberCount m
            else if m % 6 = 1 ∨ m % 6 = 5 then Omega.Conclusion.noncontractibleSecondFiberCount m
            else Omega.Conclusion.noncontractibleThirdFiberCount m := by
  refine ⟨?_, ?_⟩
  · simpa using Omega.paper_fold_bin_max_fiber_exponent.2
  · intro m hm
    have hmod : m % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases hm6 : m % 6 <;>
      simp [Omega.Conclusion.noncontractibleFiberCount, hm6]

end Omega.POM
