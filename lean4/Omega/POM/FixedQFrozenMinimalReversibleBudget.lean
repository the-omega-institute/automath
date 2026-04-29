import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Omega.Folding.MaxFiber
import Omega.POM.FixedQFrozenUniversalReversibleThreshold

namespace Omega.POM

open Filter
open scoped Topology

/-- The concrete maximal-fiber scale used by the frozen reversible-budget package. -/
noncomputable def pom_fixedq_frozen_minimal_reversible_budget_maxFiber (m : ℕ) : ℕ :=
  Omega.X.maxFiberMultiplicity m

/-- The minimal code budget at frozen parameter `s`, rounded up to the nearest whole codeword. -/
noncomputable def pom_fixedq_frozen_minimal_reversible_budget_codeBudget (s : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil (s * (pom_fixedq_frozen_minimal_reversible_budget_maxFiber m : ℝ))

/-- Paper label: `cor:pom-fixedq-frozen-minimal-reversible-budget`.
Once the maximal-fiber scale diverges, the ceiling-rounded frozen code budget has asymptotic
density `s` relative to that scale. -/
theorem paper_pom_fixedq_frozen_minimal_reversible_budget (s : ℝ) (hs : 0 < s ∧ s ≤ 1)
    (hM :
      Filter.Tendsto
        (fun m => (pom_fixedq_frozen_minimal_reversible_budget_maxFiber m : ℝ))
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun m =>
        (pom_fixedq_frozen_minimal_reversible_budget_codeBudget s m : ℝ) /
          pom_fixedq_frozen_minimal_reversible_budget_maxFiber m)
      Filter.atTop (𝓝 s) := by
  have hs0 : 0 ≤ s := hs.1.le
  simpa [pom_fixedq_frozen_minimal_reversible_budget_codeBudget, mul_comm, mul_left_comm, mul_assoc]
    using (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := s) hs0).comp hM

end Omega.POM
