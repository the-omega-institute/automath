import Omega.RecursiveAddressing.NonNullReadoutCriterionAPAL

namespace Omega.RecursiveAddressing.GluingFailureNonNullReadoutCriterionAPAL

open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Gluing-failure publication wrapper for the non-null readout criterion corollary.
    cor:nonnull-readout-criterion -/
theorem paper_gluing_failure_nonnull_readout_criterion_apal
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    {p : State} {r : Ref} {v : Value}
    (hAdm : r ∈ Adm p) (hVis : Vis p r = {v}) :
    typedReadout Adm Vis p r = Readout.value v :=
  Omega.RecursiveAddressing.NonNullReadoutCriterionAPAL.paper_information_state_nonnull_readout_criterion_apal
    Adm Vis hAdm hVis

end Omega.RecursiveAddressing.GluingFailureNonNullReadoutCriterionAPAL
