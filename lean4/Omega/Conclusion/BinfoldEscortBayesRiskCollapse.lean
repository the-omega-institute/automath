import Mathlib.Tactic

namespace Omega.Conclusion

/-- Forward Le Cam transfer gives one signed Bayes-risk difference bound. -/
lemma conclusion_binfold_escort_bayes_risk_collapse_forward_transfer
    {Prior : Type} (riskM riskInf : Prior → ℝ) (lossNorm leCamDelta : ℝ)
    (h_forward : ∀ pi : Prior, riskInf pi ≤ riskM pi + 2 * lossNorm * leCamDelta) :
    ∀ pi : Prior, riskInf pi - riskM pi ≤ 2 * lossNorm * leCamDelta := by
  intro pi
  have h := h_forward pi
  linarith

/-- Backward Le Cam transfer gives the opposite signed Bayes-risk difference bound. -/
lemma conclusion_binfold_escort_bayes_risk_collapse_backward_transfer
    {Prior : Type} (riskM riskInf : Prior → ℝ) (lossNorm leCamDelta : ℝ)
    (h_backward : ∀ pi : Prior, riskM pi ≤ riskInf pi + 2 * lossNorm * leCamDelta) :
    ∀ pi : Prior, riskM pi - riskInf pi ≤ 2 * lossNorm * leCamDelta := by
  intro pi
  have h := h_backward pi
  linarith

/-- Paper label: `thm:conclusion-binfold-escort-bayes-risk-collapse`. -/
theorem paper_conclusion_binfold_escort_bayes_risk_collapse {Prior : Type}
    (riskM riskInf : Prior → ℝ) (lossNorm leCamDelta : ℝ)
    (h_nonneg : 0 ≤ 2 * lossNorm * leCamDelta)
    (h_forward : ∀ pi : Prior, riskInf pi ≤ riskM pi + 2 * lossNorm * leCamDelta)
    (h_backward : ∀ pi : Prior, riskM pi ≤ riskInf pi + 2 * lossNorm * leCamDelta) :
    ∀ pi : Prior, |riskM pi - riskInf pi| ≤ 2 * lossNorm * leCamDelta := by
  intro pi
  have h_bound_nonneg : 0 ≤ 2 * lossNorm * leCamDelta := h_nonneg
  have h_pos :
      riskM pi - riskInf pi ≤ 2 * lossNorm * leCamDelta :=
    conclusion_binfold_escort_bayes_risk_collapse_backward_transfer
      riskM riskInf lossNorm leCamDelta h_backward pi
  have h_neg :
      riskInf pi - riskM pi ≤ 2 * lossNorm * leCamDelta :=
    conclusion_binfold_escort_bayes_risk_collapse_forward_transfer
      riskM riskInf lossNorm leCamDelta h_forward pi
  have _ := h_bound_nonneg
  exact abs_sub_le_iff.mpr ⟨h_pos, h_neg⟩

end Omega.Conclusion
