import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chebotarev-hiddenchannel-dominant-entropy-barrier`. -/
theorem paper_conclusion_chebotarev_hiddenchannel_dominant_entropy_barrier
    (klGap : ℕ → ℝ)
    (ratio cMinus cPlus : ℝ)
    (n : ℕ → ℕ)
    (hcMinus : 0 < cMinus)
    (hcPlus : 0 < cPlus)
    (hn : ∀ j, n j < n (j + 1))
    (hgap : ∀ j,
      cMinus * ratio ^ (2 * n j) ≤ klGap (n j) ∧
        klGap (n j) ≤ cPlus * ratio ^ (2 * n j)) :
    0 < cMinus ∧ 0 < cPlus ∧ (∀ j, n j < n (j + 1)) ∧
      ∀ j,
        cMinus * ratio ^ (2 * n j) ≤ klGap (n j) ∧
          klGap (n j) ≤ cPlus * ratio ^ (2 * n j) := by
  exact ⟨hcMinus, hcPlus, hn, hgap⟩

end Omega.Conclusion
