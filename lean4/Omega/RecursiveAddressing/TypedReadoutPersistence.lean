import Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a non-null typed readout is stable under refinement when admissibility is
preserved and the visible fiber does not change.
    prop:typed-readout-persistence -/
theorem paper_information_state_typed_readout_persistence_seeds
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {p q : State} {r : Ref} {v : Value}
    (href : Refines q p)
    (hread : typedReadout Adm Vis p r = Readout.value v) :
    typedReadout Adm Vis q r = Readout.value v := by
  classical
  have hpAdm : r ∈ Adm p := by
    by_cases h : r ∈ Adm p
    · exact h
    · simp [typedReadout, h] at hread
  have hpSingleton : ∃ w, Vis p r = {w} := by
    by_cases h : ∃ w, Vis p r = {w}
    · exact h
    · by_cases hEmpty : Vis p r = ∅
      · simp [typedReadout, hpAdm, hEmpty] at hread
      · simp [typedReadout, hpAdm, h, hEmpty] at hread
  have hchoose : Classical.choose hpSingleton = v := by
    simpa [typedReadout, hpAdm, hpSingleton] using hread
  have hVisP : Vis p r = {v} := by
    calc
      Vis p r = {Classical.choose hpSingleton} := Classical.choose_spec hpSingleton
      _ = {v} := by simp [hchoose]
  have hAdmQ : r ∈ Adm q := hAdm href hpAdm
  have hVisQ : Vis q r = {v} := by
    rw [hVis href hpAdm, hVisP]
  exact paper_information_state_nonnull_readout_criterion_seeds Adm Vis hAdmQ hVisQ

/-- Wrapper theorem matching the focused-publication label.
    prop:typed-readout-persistence -/
theorem paper_information_state_typed_readout_persistence_package
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {p q : State} {r : Ref} {v : Value}
    (href : Refines q p)
    (hread : typedReadout Adm Vis p r = Readout.value v) :
    typedReadout Adm Vis q r = Readout.value v :=
  paper_information_state_typed_readout_persistence_seeds
    Adm Vis Refines hAdm hVis href hread

end Omega.RecursiveAddressing
