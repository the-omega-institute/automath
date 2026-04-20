import Mathlib.Tactic
import Omega.Zeta.XiZGCountingPowerSavingError
import Omega.Zeta.XiZGReciprocalHarmonicAsymptotic

namespace Omega.Zeta

/-- Concrete analytic input for the ZG Abel/residue/log-density package. The witness carries the
counting and reciprocal-harmonic data together with the positivity range of the density constant
appearing in the paper statement. -/
structure XiZGAbelResidueLogDensityWitness where
  analytic : XiZGReciprocalHarmonicData
  density_pos : 0 < analytic.deltaZG
  density_lt_one : analytic.deltaZG < 1

namespace XiZGAbelResidueLogDensityWitness

/-- Chapter-local Abel-boundary package: the residue agrees with the density constant and the
counting function satisfies the standard Perron/Abel power-saving control. -/
def abelBoundaryLaw (W : XiZGAbelResidueLogDensityWitness) : Prop :=
  W.analytic.residueAtOne = W.analytic.deltaZG ∧
    ∀ ε > 0, ∃ C > 0, ∀ x ≥ 1,
      |W.analytic.count x - W.analytic.deltaZG * x| ≤ C * Real.rpow x (1 / 2 + ε)

/-- The reciprocal harmonic sum has the logarithmic main term predicted by Abel summation. -/
def harmonicMainTerm (W : XiZGAbelResidueLogDensityWitness) : Prop :=
  ∀ ε > 0, ε < 1 / 2 → ∃ C_ZG : ℝ, ∀ X ≥ 1,
    |W.analytic.reciprocalSum X - (W.analytic.deltaZG * Real.log X + C_ZG)| ≤
      W.analytic.errorConstant ε * Real.rpow X (-1 / 2 + ε)

/-- The critical-line package keeps track of the residue normalization together with the concrete
density range `0 < δ_ZG < 1` used in the paper's convergence discussion. -/
def absoluteConvergenceCriticalLine (W : XiZGAbelResidueLogDensityWitness) : Prop :=
  W.analytic.residueAtOne = W.analytic.deltaZG ∧
    0 < W.analytic.deltaZG ∧ W.analytic.deltaZG < 1

end XiZGAbelResidueLogDensityWitness

open XiZGAbelResidueLogDensityWitness

/-- Paper label: `thm:xi-zg-abel-residue-log-density`. -/
theorem paper_xi_zg_abel_residue_log_density
    (W : XiZGAbelResidueLogDensityWitness) :
    W.abelBoundaryLaw ∧ W.harmonicMainTerm ∧ W.absoluteConvergenceCriticalLine := by
  refine ⟨?_, paper_xi_zg_reciprocal_harmonic_asymptotic W.analytic, ?_⟩
  · refine ⟨W.analytic.residue_eq_delta, ?_⟩
    exact paper_xi_zg_counting_power_saving_error W.analytic.toXiZGCountingData
  · exact ⟨W.analytic.residue_eq_delta, W.density_pos, W.density_lt_one⟩

end Omega.Zeta
