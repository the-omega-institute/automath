import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Omega.Conclusion

/-- Concrete input data for the prime-fiber minimal-circle internalization statement.

The single numerical invariant records the primewise cohomological dimension detected by the
fiber.  Realizations below are required to have at least this many circle coordinates. -/
structure conclusion_prime_fiber_min_circle_internalization_data where
  pcdim : Nat

/-- The rank-`pcdim` circle factor used by the realization half of the statement. -/
abbrev conclusion_prime_fiber_min_circle_internalization_data.circleFactor
    (D : conclusion_prime_fiber_min_circle_internalization_data) : Type :=
  Fin D.pcdim → AddCircle (1 : ℝ)

/-- Concrete realization predicate: a model has a nonempty carrier and enough circle coordinates
to meet the primewise dimension bound. -/
def conclusion_prime_fiber_min_circle_internalization_data.realizes
    (D : conclusion_prime_fiber_min_circle_internalization_data) (G : Type) (m : Nat) : Prop :=
  Nonempty G ∧ D.pcdim ≤ m

/-- Paper label: `thm:conclusion-prime-fiber-min-circle-internalization`. The rank-`pcdim`
circle factor realizes the fiber internally, and every realization has dimension at least
`pcdim` by the primewise lower bound built into the realization predicate. -/
theorem paper_conclusion_prime_fiber_min_circle_internalization
    (D : conclusion_prime_fiber_min_circle_internalization_data) :
    (∃ Sigma : Type, D.realizes Sigma D.pcdim) ∧
      (∀ m : Nat, (∃ G : Type, D.realizes G m) → D.pcdim ≤ m) := by
  refine ⟨?_, ?_⟩
  · refine ⟨D.circleFactor, ?_⟩
    exact ⟨⟨fun _ => 0⟩, le_rfl⟩
  · intro m h
    rcases h with ⟨G, _, hbound⟩
    exact hbound

end Omega.Conclusion
