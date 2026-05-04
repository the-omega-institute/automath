import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part65c-edgeworth-local-ldp-sign-lock`. -/
theorem paper_xi_time_part65c_edgeworth_local_ldp_sign_lock (kappa3 sigma : ℝ)
    (hsigma : 0 < sigma) :
    ((kappa3 / (6 * sigma ^ 3) < 0 ↔ kappa3 < 0) ∧
      (kappa3 / (6 * sigma ^ 6) < 0 ↔ kappa3 < 0)) := by
  constructor
  · have hden : 0 < 6 * sigma ^ 3 := by positivity
    constructor
    · intro h
      rcases (div_neg_iff.mp h) with ⟨_, hden_neg⟩ | ⟨hkappa, _⟩
      · exact False.elim ((not_lt_of_gt hden) hden_neg)
      · exact hkappa
    · intro hkappa
      exact div_neg_of_neg_of_pos hkappa hden
  · have hden : 0 < 6 * sigma ^ 6 := by positivity
    constructor
    · intro h
      rcases (div_neg_iff.mp h) with ⟨_, hden_neg⟩ | ⟨hkappa, _⟩
      · exact False.elim ((not_lt_of_gt hden) hden_neg)
      · exact hkappa
    · intro hkappa
      exact div_neg_of_neg_of_pos hkappa hden

end Omega.Zeta
