import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Two-body audit completeness codimension

Finite ANOVA codimension bookkeeping for the high-order summands.
-/

namespace Omega.Conclusion

open scoped BigOperators

/-- The high-order codimension sum is the filtered finite sum over subsets of cardinality at
least three.
    thm:conclusion-two-body-audit-completeness-codimension -/
theorem paper_conclusion_two_body_audit_completeness_codimension {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → ℕ) :
    (∑ S : Finset ι, if 3 ≤ S.card then (∏ i ∈ S, d i) else 0) =
      ∑ S ∈ (Finset.univ.filter (fun S : Finset ι => 3 ≤ S.card)), ∏ i ∈ S, d i := by
  classical
  rw [Finset.sum_filter]

end Omega.Conclusion
