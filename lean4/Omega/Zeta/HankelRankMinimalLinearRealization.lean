import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

open HankelMaximalMinorSyndromeData

/-- The minimal linear realization package is obtained from the already formalized maximal-minor
syndrome normal form: the syndrome spans the kernel line, determines the unique monic recurrence,
and annihilates the explicit shift companion.
    thm:xi-hankel-rank-minimal-linear-realization -/
theorem paper_xi_hankel_rank_minimal_linear_realization {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) :
    D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated := by
  exact paper_xi_hankel_maximal_minor_syndrome_normal_form_uniqueness D

end Omega.Zeta
