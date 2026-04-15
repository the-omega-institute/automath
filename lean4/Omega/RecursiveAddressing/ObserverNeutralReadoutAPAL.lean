namespace Omega.RecursiveAddressing.ObserverNeutralReadoutAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for observer-neutral transport of readout status.
    cor:observer-neutral-readout -/
theorem paper_conservative_extension_observer_neutral_readout_apal
    {Observer State Ref Value : Type}
    (liftState : (Observer → Observer) → State → State)
    (liftRef : (Observer → Observer) → Ref → Ref)
    (liftValue : (Observer → Observer) → Value → Value)
    (ReadAt : State → Ref → Value → Prop)
    (htransport : ∀ σ p r v, ReadAt p r v → ReadAt (liftState σ p) (liftRef σ r) (liftValue σ v))
    {σ : Observer → Observer} {p : State} {r : Ref} {v : Value}
    (hread : ReadAt p r v) :
    ReadAt (liftState σ p) (liftRef σ r) (liftValue σ v) :=
  htransport σ p r v hread

end Omega.RecursiveAddressing.ObserverNeutralReadoutAPAL
