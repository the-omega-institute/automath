import Mathlib.Tactic
import Omega.POM.SchurPartitionEnergyEventualQuasiperiodicLinearLaw

namespace Omega.POM

/-- The `Lstar` optimum from the quasiperiodic linear-law seed package. -/
def pom_schur_near_rh_linear_necessary_quasiperiodic_Lstar (q : ℕ) : ℕ :=
  pomSchurPartitionEnergyOptimum q

/-- The concrete pressure just saturating the square-root near-RH threshold. -/
def pom_schur_near_rh_linear_necessary_quasiperiodic_pressure (q : ℕ) : ℕ :=
  2 * pom_schur_near_rh_linear_necessary_quasiperiodic_Lstar q

/-- Near-RH in logarithmic form: the nontrivial Schur envelope is at most half the pressure. -/
def pom_schur_near_rh_linear_necessary_quasiperiodic_nearRh (q : ℕ) : Prop :=
  2 * pom_schur_near_rh_linear_necessary_quasiperiodic_Lstar q ≤
    pom_schur_near_rh_linear_necessary_quasiperiodic_pressure q

/-- The eventual quasiperiodic linear lower bound `2 q a_* + 2 β(q mod g)`. -/
def pom_schur_near_rh_linear_necessary_quasiperiodic_linearLowerBound (q : ℕ) : ℕ :=
  2 * (q * pomSchurPeakSlope - pomSchurDeficit (q % pomSchurPeakPeriod))

/-- Paper-facing corollary package for the quasiperiodic linear near-RH necessary condition. -/
def pom_schur_near_rh_linear_necessary_quasiperiodic_statement : Prop :=
  PomSchurPartitionEnergyEventualQuasiperiodicLinearLaw ∧
    ∀ q : ℕ,
      pom_schur_near_rh_linear_necessary_quasiperiodic_nearRh q →
        2 * pom_schur_near_rh_linear_necessary_quasiperiodic_Lstar q ≤
          pom_schur_near_rh_linear_necessary_quasiperiodic_pressure q ∧
        pom_schur_near_rh_linear_necessary_quasiperiodic_pressure q =
          pom_schur_near_rh_linear_necessary_quasiperiodic_linearLowerBound q

/-- Paper label: `cor:pom-schur-near-rh-linear-necessary-quasiperiodic`. -/
theorem paper_pom_schur_near_rh_linear_necessary_quasiperiodic :
    pom_schur_near_rh_linear_necessary_quasiperiodic_statement := by
  refine ⟨paper_pom_schur_partition_energy_eventual_quasiperiodic_linear_law, ?_⟩
  intro q hNearRh
  refine ⟨hNearRh, ?_⟩
  simp [pom_schur_near_rh_linear_necessary_quasiperiodic_pressure,
    pom_schur_near_rh_linear_necessary_quasiperiodic_Lstar,
    pom_schur_near_rh_linear_necessary_quasiperiodic_linearLowerBound,
    pomSchurPartitionEnergyOptimum, pomSchurPeakSlope, pomSchurDeficit]

end Omega.POM
