import Omega.LogicExpansionChain.NormalizationNoFactCreation

namespace Omega.LogicExpansionChain.ConcreteNormalizationNoFactCreation

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the concrete normalization no-fact-creation corollary.
    cor:concrete-normalization-no-fact-creation -/
theorem paper_conservative_extension_concrete_normalization_no_fact_creation_apal
    {AbstractState ConcreteState AbstractExpr ConcreteExpr AbstractValue ConcreteValue : Type}
    (interpState : AbstractState → ConcreteState)
    (interpExpr : AbstractExpr → ConcreteExpr)
    (interpValue : AbstractValue → ConcreteValue)
    (readAbstract : AbstractState → AbstractExpr → Option AbstractValue)
    (readConcrete : ConcreteState → ConcreteExpr → Option ConcreteValue)
    (p : AbstractState) {n : Nat} (E : Nat → AbstractExpr)
    (hstep : ∀ i, i < n → ∀ v, readAbstract p (E (i + 1)) = some v → readAbstract p (E i) = some v)
    (htransport : ∀ e v,
      readAbstract p e = some v ↔
        readConcrete (interpState p) (interpExpr e) = some (interpValue v))
    {v : AbstractValue}
    (hend : readConcrete (interpState p) (interpExpr (E n)) = some (interpValue v)) :
    readConcrete (interpState p) (interpExpr (E 0)) = some (interpValue v) := by
  have hAbstractEnd : readAbstract p (E n) = some v := (htransport (E n) v).mpr hend
  have hAbstractStart :
      readAbstract p (E 0) = some v :=
    Omega.LogicExpansionChain.paper_conservative_extension_normalization_no_fact_creation_seeds
      readAbstract p E hstep hAbstractEnd
  exact (htransport (E 0) v).mp hAbstractStart

end Omega.LogicExpansionChain.ConcreteNormalizationNoFactCreation
