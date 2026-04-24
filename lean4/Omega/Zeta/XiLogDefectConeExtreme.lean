import Omega.Zeta.XiDefectDensityConeChoquetExtreme
import Omega.Zeta.XiLogdefectConeChoquetBauerCompleteness

namespace Omega.Zeta

/-- Concrete paper-facing package for the finite log-defect cone: the already verified
Choquet--Bauer completeness statement supplies uniqueness of the one-kernel decomposition, and the
finite atomic cone wrapper identifies the extremal rays with the Dirac generators. -/
def xi_log_defect_cone_extreme_statement : Prop :=
  XiLogdefectChoquetBauerFiniteCompleteness ∧
    ∀ D : XiDefectDensityConeData,
      D.injectiveCoding ∧ D.extremeRaysAreDirac ∧ D.integerMultiplicityLattice

/-- Paper label: `cor:xi-log-defect-cone-extreme`. -/
theorem paper_xi_log_defect_cone_extreme : xi_log_defect_cone_extreme_statement := by
  refine ⟨paper_xi_logdefect_cone_choquet_bauer_completeness, ?_⟩
  intro D
  exact paper_xi_defect_density_cone_choquet_extreme D

end Omega.Zeta
