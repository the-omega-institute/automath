import Mathlib.Data.Nat.Choose.Multinomial
import Omega.POM.MicrocanonicalCoverTimeTailInclusionExclusion

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The labeled fold-class count with prescribed fiber-size profile `d`. -/
def microcanonicalFoldClassCount (d : α → ℕ) : ℕ :=
  Nat.multinomial (Finset.univ : Finset α) d

set_option maxHeartbeats 400000 in
/-- The fold class with fiber sizes `d(x)` has multinomial cardinality.
    thm:pom-microcanonical-fold-class-count -/
theorem paper_pom_microcanonical_fold_class_count (d : α → ℕ) :
    (∏ x ∈ (Finset.univ : Finset α), Nat.factorial (d x)) * microcanonicalFoldClassCount d =
        Nat.factorial (microcanonicalTotalMass d) ∧
      microcanonicalFoldClassCount d =
        Nat.factorial (microcanonicalTotalMass d) /
          ∏ x ∈ (Finset.univ : Finset α), Nat.factorial (d x) := by
  constructor
  · simpa [microcanonicalFoldClassCount, microcanonicalTotalMass] using
      (Nat.multinomial_spec (s := (Finset.univ : Finset α)) (f := d))
  · simp [microcanonicalFoldClassCount, microcanonicalTotalMass, Nat.multinomial]

end

end Omega.POM
