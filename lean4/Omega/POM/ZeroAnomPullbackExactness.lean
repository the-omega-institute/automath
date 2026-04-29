import Mathlib.Tactic

namespace Omega.POM

/-- Concrete closed-loop residual interface for zero anomaly versus Beck--Chevalley exactness. -/
structure pom_zero_anom_pullback_exactness_data where
  anomalyResidual : ℝ
  beckChevalleyResidual : ℝ
  observableResidual_eq : anomalyResidual = beckChevalleyResidual

namespace pom_zero_anom_pullback_exactness_data

/-- Vanishing of the observable anomaly residual. -/
def zeroAnomaly (D : pom_zero_anom_pullback_exactness_data) : Prop :=
  D.anomalyResidual = 0

/-- Exactness of the Beck--Chevalley comparison square at the closed-loop interface. -/
def beckChevalleyExact (D : pom_zero_anom_pullback_exactness_data) : Prop :=
  D.beckChevalleyResidual = 0

end pom_zero_anom_pullback_exactness_data

/-- Paper label: `cor:pom-zero-anom-pullback-exactness`. Since the anomaly residual is exactly
the observable residual of the Beck--Chevalley square, vanishing of one is equivalent to
exactness of the other. -/
theorem paper_pom_zero_anom_pullback_exactness (D : pom_zero_anom_pullback_exactness_data) :
    D.zeroAnomaly ↔ D.beckChevalleyExact := by
  dsimp [pom_zero_anom_pullback_exactness_data.zeroAnomaly,
    pom_zero_anom_pullback_exactness_data.beckChevalleyExact]
  rw [D.observableResidual_eq]

end Omega.POM
