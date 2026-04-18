import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

open HankelMaximalMinorSyndromeData

namespace HankelMaximalMinorSyndromeData

/-- Concrete rank/linear-recurrence package extracted from the maximal-minor syndrome normal
form: the syndrome generates the kernel line, the normalized monic recurrence is unique, and the
shift companion is annihilated by that recurrence. -/
def rankLinearRecurrenceCriterion {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) : Prop :=
  D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated

end HankelMaximalMinorSyndromeData

/-- Vanishing higher Hankel minors produce the kernel-line syndrome, the unique normalized linear
recurrence, and the annihilated shift companion package already formalized in the syndrome normal
form theorem.
    thm:xi-hankel-rank-linear-recurrence -/
theorem paper_xi_hankel_rank_linear_recurrence {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) : D.rankLinearRecurrenceCriterion := by
  exact paper_xi_hankel_maximal_minor_syndrome_normal_form_uniqueness D

end Omega.Zeta
