import Mathlib.Tactic

namespace Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

/-- Output type for the typed readout used in the paper-facing seed. -/
inductive Readout (Value : Type)
  | undefined
  | null
  | value (v : Value)
deriving DecidableEq

/-- A direct formalization of the typed-readout definition restricted to the cases needed for the
paper corollary. -/
noncomputable def typedReadout
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value) (p : State) (r : Ref) :
    Readout Value := by
  classical
  exact
    if hAdm : r ∈ Adm p then
      if hSingleton : ∃ v, Vis p r = {v} then
        Readout.value (Classical.choose hSingleton)
      else if hEmpty : Vis p r = ∅ then
        Readout.null
      else
        Readout.undefined
    else
      Readout.undefined

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: admissibility plus a singleton visible fiber forces a non-null readout.
    cor:nonnull-readout-criterion -/
theorem paper_information_state_nonnull_readout_criterion_seeds
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    {p : State} {r : Ref} {v : Value}
    (hAdm : r ∈ Adm p) (hVis : Vis p r = {v}) :
    typedReadout Adm Vis p r = Readout.value v := by
  classical
  let hs : ∃ w, Vis p r = {w} := ⟨v, hVis⟩
  have hchooseEq : Classical.choose hs = v := by
    have hspec : Vis p r = {Classical.choose hs} := Classical.choose_spec hs
    exact Set.singleton_injective (hspec.symm.trans hVis)
  simp [typedReadout, hAdm, hs, hchooseEq]

/-- Wrapper theorem matching the focused-publication label.
    cor:nonnull-readout-criterion -/
theorem paper_information_state_nonnull_readout_criterion_package
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    {p : State} {r : Ref} {v : Value}
    (hAdm : r ∈ Adm p) (hVis : Vis p r = {v}) :
    typedReadout Adm Vis p r = Readout.value v :=
  paper_information_state_nonnull_readout_criterion_seeds Adm Vis hAdm hVis

end Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion
