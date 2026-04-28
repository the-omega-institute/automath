import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9d-clark-jensen-reversekl-identity`. -/
theorem paper_xi_time_part9d_clark_jensen_reversekl_identity (D KL logTerm : ℝ)
    (hidentity : D = (1 / 2 : ℝ) * KL + (1 / 2 : ℝ) * logTerm) (hD_nonneg : 0 ≤ D)
    (hlog_nonpos : logTerm ≤ 0) :
    D = (1 / 2 : ℝ) * KL + (1 / 2 : ℝ) * logTerm ∧ 0 ≤ D ∧
      D ≤ (1 / 2 : ℝ) * KL := by
  refine ⟨hidentity, hD_nonneg, ?_⟩
  linarith

end Omega.Zeta
