import Omega.POM.CountertermAnomalyCancellation

namespace Omega.POM

/-- Paper-facing strictification wrapper: choose the counterterm `η = - anomaly`, then the
relative anomaly vanishes, the pole layer is unchanged, and the finite drift is translated by the
anomaly. The pole mass is therefore invariant under the strictification gate.
    thm:pom-strictification-splitting -/
theorem paper_pom_strictification_splitting (n : ℕ) (pole finiteDrift anomaly : Fin n → ℝ) :
    let η : Fin n → ℝ := fun i => -anomaly i
    let gate := pom_counterterm_anom_cancel_counterterm_gate pole finiteDrift η
    pom_counterterm_anom_cancel_relative_anomaly anomaly η = 0 ∧
      gate.1 = pole ∧
      gate.2 = (fun i => finiteDrift i - anomaly i) ∧
      pom_counterterm_anom_cancel_pole_mass gate.1 = pom_counterterm_anom_cancel_pole_mass pole := by
  simpa using paper_pom_counterterm_anom_cancel n pole finiteDrift anomaly

end Omega.POM
