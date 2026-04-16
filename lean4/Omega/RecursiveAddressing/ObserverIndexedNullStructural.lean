import Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Unfolding the observer-indexed typed readout shows that the `NULL` branch is exactly the
admissible-address plus empty-visible-fiber case.
    prop:observer-indexed-null-structural -/
theorem paper_recursive_addressing_observer_indexed_null_structural
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    {p : State} {r : Ref} :
    typedReadout Adm Vis p r = Readout.null ↔ r ∈ Adm p ∧ Vis p r = ∅ := by
  classical
  by_cases hAdm : r ∈ Adm p
  · by_cases hSingleton : ∃ v, Vis p r = {v}
    · rcases hSingleton with ⟨v, hv⟩
      simp [typedReadout, hAdm, hv]
    · by_cases hEmpty : Vis p r = ∅
      · simp [typedReadout, hAdm, hEmpty]
      · simp [typedReadout, hAdm, hSingleton, hEmpty]
  · simp [typedReadout, hAdm]

end Omega.RecursiveAddressing
