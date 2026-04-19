import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- Paper-facing critical-line corollary extracted from the Abel/residue/log-density package. -/
def xiZGAbsoluteConvergenceCriticalLineStatement
    (W : XiZGAbelResidueLogDensityWitness) : Prop :=
  W.absoluteConvergenceCriticalLine

/-- Paper label: `cor:xi-zg-absolute-convergence-critical-line`. -/
theorem paper_xi_zg_absolute_convergence_critical_line
    (W : XiZGAbelResidueLogDensityWitness) :
    xiZGAbsoluteConvergenceCriticalLineStatement W := by
  exact (paper_xi_zg_abel_residue_log_density W).2.2

end Omega.Zeta
