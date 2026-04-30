import Omega.RecursiveAddressing.TypedReadoutPersistence
import Omega.RecursiveAddressing.AddressBeforeValue

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

set_option maxHeartbeats 400000 in
/-- Paper-label wrapper for `prop:observer-indexed-readout-forcing-criterion`. -/
theorem paper_observer_indexed_readout_forcing_criterion
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
  exact paper_recursive_addressing_observer_indexed_readout_forcing_criterion
    Adm Vis Refines hAdm hVis href

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: a typed readout is non-`NULL` exactly when the reference is admissible
and the local witness set is nonempty. The companion negative statement is the address-before-value
specialization: if admissibility fails or the witness fiber is empty, then no non-`NULL` readout
can be forced.
    cor:observer-indexed-nonnull-criterion -/
theorem paper_recursive_addressing_observer_indexed_nonnull_criterion
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    {p : State} {r : Ref} :
    (((∃ v, typedReadout Adm Vis p r = Readout.value v) ↔
        (r ∈ Adm p ∧ (Γ p r).Nonempty)) ∧
      ((r ∉ Adm p ∨ Γ p r = ∅) →
        ¬ ∃ v, typedReadout Adm Vis p r = Readout.value v)) := by
  classical
  have hWitness :
      ∀ {s : State} {a : Ref}, (∃ v, Vis s a = {v}) ↔ (Γ s a).Nonempty := by
    intro s a
    constructor
    · rintro ⟨v, hv⟩
      rw [hΓ s a]
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rw [hΓ s a] at hv
      exact hv
  have hCriterion :
      (∃ v, typedReadout Adm Vis p r = Readout.value v) ↔
        (r ∈ Adm p ∧ ∃ v, Vis p r = {v}) := by
    simpa using
      (paper_recursive_addressing_observer_indexed_readout_forcing_criterion
        Adm Vis
        (fun q p => q = p)
        (by
          intro p q r hEq hr
          simpa [hEq] using hr)
        (by
          intro p q r hEq hr
          simpa [hEq] using rfl)
        (p := p) (q := p) (r := r) rfl).1
  have hReadoutAddr :
      ∀ {s : State} {a : Ref} {v : Value},
        typedReadout Adm Vis s a = Readout.value v → a ∈ Adm s := by
    intro s a v hread
    have hCriterion' :
        (∃ w, typedReadout Adm Vis s a = Readout.value w) ↔
          (a ∈ Adm s ∧ ∃ w, Vis s a = {w}) := by
      simpa using
        (paper_recursive_addressing_observer_indexed_readout_forcing_criterion
          Adm Vis
          (fun q p => q = p)
          (by
            intro p q r hEq hr
            simpa [hEq] using hr)
          (by
            intro p q r hEq hr
            simpa [hEq] using rfl)
          (p := s) (q := s) (r := a) rfl).1
    exact (hCriterion'.mp ⟨v, hread⟩).1
  have hReadoutWitness :
      ∀ {s : State} {a : Ref} {v : Value},
        typedReadout Adm Vis s a = Readout.value v → (Γ s a).Nonempty := by
    intro s a v hread
    have hCriterion' :
        (∃ w, typedReadout Adm Vis s a = Readout.value w) ↔
          (a ∈ Adm s ∧ ∃ w, Vis s a = {w}) := by
      simpa using
        (paper_recursive_addressing_observer_indexed_readout_forcing_criterion
          Adm Vis
          (fun q p => q = p)
          (by
            intro p q r hEq hr
            simpa [hEq] using hr)
          (by
            intro p q r hEq hr
            simpa [hEq] using rfl)
          (p := s) (q := s) (r := a) rfl).1
    exact (hWitness (s := s) (a := a)).mp (hCriterion'.mp ⟨v, hread⟩).2
  refine ⟨?_, ?_⟩
  · constructor
    · intro hread
      rcases hCriterion.mp hread with ⟨hAdm, hVis⟩
      exact ⟨hAdm, (hWitness (s := p) (a := r)).mp hVis⟩
    · rintro ⟨hAdm, hNonempty⟩
      exact hCriterion.mpr ⟨hAdm, (hWitness (s := p) (a := r)).mpr hNonempty⟩
  · intro hbad hread
    rcases hread with ⟨v, hread⟩
    exact (AddressBeforeValue.paper_observer_indexed_address_before_value_package
      Adm Γ (fun s a v => typedReadout Adm Vis s a = Readout.value v)
      (by
        intro s a v h
        exact hReadoutAddr h)
      (by
        intro s a v h
        exact hReadoutWitness h)
      (p := p) (a := r) (v := v) hbad) hread

end Omega.RecursiveAddressing
