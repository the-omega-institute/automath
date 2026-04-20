import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite counting package for fold inversion with `sideBits` bits of auxiliary information. The
visible output identifies at most `observableCount` fibers, each fiber can be refined into at most
`2^sideBits` microstates by the side information, and `distinguishableCount` records the resulting
total number of microstates that can be singled out. -/
structure XiFoldInversionStrongConverseSideinfoData where
  sideBits : ℕ
  observableCount : ℕ
  wordLength : ℕ
  distinguishableCount : ℕ
  successProb : ℚ
  distinguishable_le : distinguishableCount ≤ 2 ^ sideBits * observableCount
  successProb_le_count : successProb ≤ distinguishableCount / (2 : ℚ) ^ wordLength

/-- Paper label: `thm:xi-fold-inversion-strong-converse-sideinfo`. -/
theorem paper_xi_fold_inversion_strong_converse_sideinfo
    (h : XiFoldInversionStrongConverseSideinfoData) :
    h.successProb <= (2 : Rat) ^ h.sideBits * h.observableCount / (2 : Rat) ^ h.wordLength := by
  have hcount :
      (h.distinguishableCount : ℚ) <= (2 : ℚ) ^ h.sideBits * h.observableCount := by
    exact_mod_cast h.distinguishable_le
  have hdiv :
      (h.distinguishableCount : ℚ) / (2 : ℚ) ^ h.wordLength <=
        ((2 : ℚ) ^ h.sideBits * h.observableCount) / (2 : ℚ) ^ h.wordLength := by
    exact div_le_div_of_nonneg_right hcount (by positivity)
  exact le_trans h.successProb_le_count hdiv

end Omega.Zeta
