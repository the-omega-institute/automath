namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: typed readouts transport through a realization map preserving readout
    values.
    prop:readout-transport -/
theorem paper_conservative_extension_readout_transport_seeds
    {AbstractState ConcreteState AbstractRef ConcreteRef AbstractValue ConcreteValue : Type}
    (interpState : AbstractState → ConcreteState)
    (interpRef : AbstractRef → ConcreteRef)
    (interpValue : AbstractValue → ConcreteValue)
    (readAbstract : AbstractState → AbstractRef → Option AbstractValue)
    (readConcrete : ConcreteState → ConcreteRef → Option ConcreteValue)
    (htransport : ∀ p r v,
      readAbstract p r = some v ↔
        readConcrete (interpState p) (interpRef r) = some (interpValue v))
    {p : AbstractState} {r : AbstractRef} {v : AbstractValue}
    (hread : readAbstract p r = some v) :
    readConcrete (interpState p) (interpRef r) = some (interpValue v) :=
  (htransport p r v).mp hread

/-- Packaged form of the typed-readout transport seed.
    prop:readout-transport -/
theorem paper_conservative_extension_readout_transport_package
    {AbstractState ConcreteState AbstractRef ConcreteRef AbstractValue ConcreteValue : Type}
    (interpState : AbstractState → ConcreteState)
    (interpRef : AbstractRef → ConcreteRef)
    (interpValue : AbstractValue → ConcreteValue)
    (readAbstract : AbstractState → AbstractRef → Option AbstractValue)
    (readConcrete : ConcreteState → ConcreteRef → Option ConcreteValue)
    (htransport : ∀ p r v,
      readAbstract p r = some v ↔
        readConcrete (interpState p) (interpRef r) = some (interpValue v))
    {p : AbstractState} {r : AbstractRef} {v : AbstractValue}
    (hread : readAbstract p r = some v) :
    readConcrete (interpState p) (interpRef r) = some (interpValue v) :=
  paper_conservative_extension_readout_transport_seeds
    interpState interpRef interpValue readAbstract readConcrete htransport hread

end Omega.LogicExpansionChain
