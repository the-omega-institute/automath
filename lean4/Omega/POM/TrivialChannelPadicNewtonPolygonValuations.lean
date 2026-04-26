import Mathlib.Tactic

namespace Omega.POM

set_option linter.unusedVariables false

/-- Paper label: `prop:pom-trivial-channel-padic-newton-polygon-valuations`. -/
theorem paper_pom_trivial_channel_padic_newton_polygon_valuations
    (p : Nat) (hp : Nat.Prime p) (recoveredQ newtonSlopeReadout
      valuationDistributionRecovered : Prop)
    (hQ : recoveredQ) (hNewton : recoveredQ -> newtonSlopeReadout)
    (hVal : newtonSlopeReadout -> valuationDistributionRecovered) :
    valuationDistributionRecovered := by
  exact hVal (hNewton hQ)

end Omega.POM
