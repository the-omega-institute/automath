import Omega.Zeta.XiFoldEscortLogMultiplicityTwoAtom

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part54ab-escort-logdefect-moments`. The escort log-defect moments
are exactly the mean and variance clauses of the previously verified two-atom law. -/
theorem paper_xi_time_part54ab_escort_logdefect_moments (q : ℝ) :
    xiFoldEscortLogMultiplicityMean q = -(Real.log Real.goldenRatio) *
        Omega.Folding.killoEscortTheta q ∧
      xiFoldEscortLogMultiplicityVariance q = (Real.log Real.goldenRatio) ^ 2 *
        Omega.Folding.killoEscortTheta q * (1 - Omega.Folding.killoEscortTheta q) := by
  have h := paper_xi_fold_escort_log_multiplicity_two_atom q
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

end Omega.Zeta
