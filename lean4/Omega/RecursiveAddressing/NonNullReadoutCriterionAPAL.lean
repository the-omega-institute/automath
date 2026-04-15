import Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

namespace Omega.RecursiveAddressing.NonNullReadoutCriterionAPAL

open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the non-null readout criterion corollary.
    cor:nonnull-readout-criterion -/
theorem paper_information_state_nonnull_readout_criterion_apal
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    {p : State} {r : Ref} {v : Value}
    (hAdm : r ∈ Adm p) (hVis : Vis p r = {v}) :
    typedReadout Adm Vis p r = Readout.value v :=
  paper_information_state_nonnull_readout_criterion_seeds Adm Vis hAdm hVis

end Omega.RecursiveAddressing.NonNullReadoutCriterionAPAL
