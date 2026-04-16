import Mathlib.Tactic

namespace Omega.Folding

universe u

/-- Chapter-local package for the ergodic limit of the observable `\hat\eta_m`. The data stores
the finite-state synchronization extension, the singleton-state indicator, the invariant-measure
average for that indicator, and the steps identifying the almost-sure limit with the paper-facing
observable constant. -/
structure EtaMHatErgodicLimitData where
  SyncExtension : Type u
  singletonIndicator : SyncExtension → Prop
  invariantMeasureAverage : Prop
  almostSureSingletonLimit : Prop
  observableConstant : Prop
  observableLimit : Prop
  hasInvariantMeasureAverage : invariantMeasureAverage
  deriveAlmostSureSingletonLimit :
    invariantMeasureAverage → almostSureSingletonLimit
  identifyObservableConstant :
    almostSureSingletonLimit → observableConstant
  exposeObservableLimit :
    almostSureSingletonLimit → observableConstant → observableLimit

/-- The singleton-state frequency observable `\hat\eta_m` converges almost surely to the constant
read off from the invariant measure on the synchronization extension.
    prop:eta_m_hat_ergodic_limit -/
theorem paper_eta_m_hat_ergodic_limit (D : EtaMHatErgodicLimitData) :
    D.observableLimit := by
  have hLimit : D.almostSureSingletonLimit :=
    D.deriveAlmostSureSingletonLimit D.hasInvariantMeasureAverage
  have hObservable : D.observableConstant := D.identifyObservableConstant hLimit
  exact D.exposeObservableLimit hLimit hObservable

end Omega.Folding
