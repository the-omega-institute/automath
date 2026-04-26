import Omega.GU.LogCmNoFixedLinearRecurrence

namespace Omega.GroupUnification

/-- Group-unification wrapper for the already verified GU recurrence obstruction. -/
def gut_logcm_no_fixed_linear_recurrence_statement : Prop :=
  ¬ ∃ k : ℕ, 0 < k ∧ Omega.GU.gutLogCmFixedLinearRecurrence k

lemma gut_logcm_no_fixed_linear_recurrence_proof :
    gut_logcm_no_fixed_linear_recurrence_statement := by
  simpa [gut_logcm_no_fixed_linear_recurrence_statement] using
    Omega.GU.paper_gut_logCm_no_fixed_linear_recurrence

/-- Paper label: `thm:gut-logCm-no-fixed-linear-recurrence`. -/
theorem paper_gut_logcm_no_fixed_linear_recurrence :
    gut_logcm_no_fixed_linear_recurrence_statement :=
  gut_logcm_no_fixed_linear_recurrence_proof

end Omega.GroupUnification
