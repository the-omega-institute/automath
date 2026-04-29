import Omega.Zeta.HankelRankMinimalLinearRealization

namespace Omega.Zeta

open HankelMaximalMinorSyndromeData

/-- The scan Hankel rank equals the finite defect count, exposed as the paper-facing wrapper
around the maximal-minor/minimal-realization Hankel package.
    con:xi-scan-hankel-rank-equals-defect -/
theorem paper_xi_scan_hankel_rank_equals_defect {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) :
    D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated := by
  exact paper_xi_hankel_rank_minimal_linear_realization D

end Omega.Zeta
