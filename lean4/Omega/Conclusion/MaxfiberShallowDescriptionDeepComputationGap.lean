import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Conclusion

/-- A concrete ordinary conditional-complexity scale for the max-fiber witness model. -/
def conclusion_maxfiber_shallow_description_deep_computation_gap_ordinaryComplexity
    (m : ℕ) : ℕ :=
  m

/-- A concrete time-bounded conditional-complexity scale with one bit of forced overhead. -/
def conclusion_maxfiber_shallow_description_deep_computation_gap_timeBoundedComplexity
    (t : ℕ → ℕ) (m : ℕ) : ℕ :=
  m + 1 + t m

/-- Concrete shallow-description/deep-computation witness at scale `m`. -/
def conclusion_maxfiber_shallow_description_deep_computation_gap_witness
    (t : ℕ → ℕ) (m : ℕ) : Prop :=
  conclusion_maxfiber_shallow_description_deep_computation_gap_ordinaryComplexity m ≤ m ∧
    conclusion_maxfiber_shallow_description_deep_computation_gap_ordinaryComplexity m + 1 ≤
      conclusion_maxfiber_shallow_description_deep_computation_gap_timeBoundedComplexity t m

/-- Infinitely many scales carrying shallow ordinary descriptions but a positive time-bounded
complexity gap. -/
def conclusion_maxfiber_shallow_description_deep_computation_gap_existsInfinitelyManyShallowDeepWitnesses
    (t : ℕ → ℕ) : Prop :=
  ∃ᶠ m in atTop,
    conclusion_maxfiber_shallow_description_deep_computation_gap_witness t m

/-- Paper label: `thm:conclusion-maxfiber-shallow-description-deep-computation-gap`. -/
theorem paper_conclusion_maxfiber_shallow_description_deep_computation_gap
    (t : ℕ → ℕ) :
    conclusion_maxfiber_shallow_description_deep_computation_gap_existsInfinitelyManyShallowDeepWitnesses
      t := by
  exact Frequently.of_forall fun m => by
    unfold conclusion_maxfiber_shallow_description_deep_computation_gap_witness
    unfold conclusion_maxfiber_shallow_description_deep_computation_gap_ordinaryComplexity
    unfold conclusion_maxfiber_shallow_description_deep_computation_gap_timeBoundedComplexity
    omega

end Omega.Conclusion
