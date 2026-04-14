import Omega.RecursiveAddressing.TypedReadoutPersistence

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing observer-indexed readout criterion: a typed readout is non-null exactly when the
reference is admissible with singleton visibility, and this non-null readout persists under
refinement.
    prop:observer-indexed-readout-forcing-criterion -/
theorem paper_recursive_addressing_observer_indexed_readout_forcing_criterion
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {p q : State} {r : Ref} (href : Refines q p) :
    (((∃ v, typedReadout Adm Vis p r = Readout.value v) ↔
        (r ∈ Adm p ∧ ∃ v, Vis p r = {v})) ∧
      ((∃ v, typedReadout Adm Vis p r = Readout.value v) →
        ∃ v, typedReadout Adm Vis q r = Readout.value v)) := by
  classical
  constructor
  · constructor
    · rintro ⟨v, hread⟩
      by_cases hAdmP : r ∈ Adm p
      · by_cases hSingleton : ∃ w, Vis p r = {w}
        · exact ⟨hAdmP, hSingleton⟩
        · by_cases hEmpty : Vis p r = ∅
          · simp [typedReadout, hAdmP, hEmpty] at hread
          · simp [typedReadout, hAdmP, hSingleton, hEmpty] at hread
      · simp [typedReadout, hAdmP] at hread
    · rintro ⟨hAdmP, hSingleton⟩
      rcases hSingleton with ⟨v, hVisP⟩
      exact ⟨v, paper_information_state_nonnull_readout_criterion_seeds Adm Vis hAdmP hVisP⟩
  · intro hread
    rcases hread with ⟨v, hread⟩
    exact ⟨v, paper_information_state_typed_readout_persistence_seeds
      Adm Vis Refines hAdm hVis href hread⟩

end Omega.RecursiveAddressing
