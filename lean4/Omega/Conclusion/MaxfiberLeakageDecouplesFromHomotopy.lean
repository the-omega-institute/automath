import Mathlib.Tactic
import Omega.POM.MaxNoncontractibleFiberMod6Phase

namespace Omega.Conclusion

/-- Concrete conclusion data for the decoupling wrapper.  The leakage side is a rational
limit profile with a positive odd leakage constant; the homotopy side is the existing
noncontractible `m mod 6` phase decomposition. -/
structure conclusion_maxfiber_leakage_decouples_from_homotopy_data where
  oddLeakageConstant : ℚ
  oddLeakageConstant_pos : 0 < oddLeakageConstant
  leakageLimit :
    ∀ m : ℕ,
      17 ≤ m →
        0 ≤ oddLeakageConstant +
          (noncontractibleFiberCount m : ℚ) / noncontractibleMainFiberCount m

/-- The concrete conclusion statement: the leakage profile has a positive odd constant and
nonnegative limiting defect, while the homotopy classification is exactly the already audited
mod-`6` noncontractible phase split. -/
def conclusion_maxfiber_leakage_decouples_from_homotopy_data.statement
    (D : conclusion_maxfiber_leakage_decouples_from_homotopy_data) : Prop :=
  0 < D.oddLeakageConstant ∧
    (∀ m : ℕ,
      17 ≤ m →
        0 ≤ D.oddLeakageConstant +
          (noncontractibleFiberCount m : ℚ) / noncontractibleMainFiberCount m) ∧
      (∀ m : ℕ,
        17 ≤ m →
          (m % 6 = 0 ∨ m % 6 = 4) →
            noncontractibleFiberCount m = noncontractibleMainFiberCount m) ∧
        (∀ m : ℕ,
          17 ≤ m →
            (m % 6 = 1 ∨ m % 6 = 5) →
              noncontractibleFiberCount m = noncontractibleSecondFiberCount m) ∧
          (∀ m : ℕ,
            17 ≤ m →
              (m % 6 = 2 ∨ m % 6 = 3) →
                noncontractibleFiberCount m = noncontractibleThirdFiberCount m)

/-- Paper label: `thm:conclusion-maxfiber-leakage-decouples-from-homotopy`.
The leakage hypotheses provide the positive odd constant and limiting nonnegativity, while the
homotopy phase clauses are exactly the existing noncontractible `m mod 6` split. -/
theorem paper_conclusion_maxfiber_leakage_decouples_from_homotopy
    (D : conclusion_maxfiber_leakage_decouples_from_homotopy_data) : D.statement := by
  rcases Omega.POM.paper_pom_max_noncontractible_fiber_mod6_phase with
    ⟨hMain, hSecond, hThird⟩
  exact ⟨D.oddLeakageConstant_pos, D.leakageLimit, hMain, hSecond, hThird⟩

end Omega.Conclusion
