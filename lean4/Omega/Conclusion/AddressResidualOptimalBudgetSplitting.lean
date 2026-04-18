import Mathlib.Tactic

namespace Omega.Conclusion

/-- The lower envelope of the decreasing line `L - m` and the increasing line `1 + γ m`
is minimized at their unique intersection.
    thm:conclusion-address-residual-optimal-budget-splitting -/
theorem paper_conclusion_address_residual_optimal_budget_splitting (L gamma : Real)
    (hgamma : 0 < gamma) :
    let mStar := (L - 1) / (1 + gamma)
    let bStar := (gamma * L + 1) / (1 + gamma)
    (∀ m : Real, max (L - m) (1 + gamma * m) >= bStar) ∧
      max (L - mStar) (1 + gamma * mStar) = bStar ∧
      mStar + bStar = L := by
  dsimp
  have hden : 0 < 1 + gamma := by linarith
  have hden_ne : (1 + gamma) ≠ 0 := ne_of_gt hden
  have hm_eq :
      L - (L - 1) / (1 + gamma) = (gamma * L + 1) / (1 + gamma) := by
    field_simp [hden_ne]
    ring
  have hb_eq :
      1 + gamma * ((L - 1) / (1 + gamma)) = (gamma * L + 1) / (1 + gamma) := by
    field_simp [hden_ne]
    ring
  have hsum :
      (L - 1) / (1 + gamma) + (gamma * L + 1) / (1 + gamma) = L := by
    field_simp [hden_ne]
    ring
  refine ⟨?_, ?_, hsum⟩
  · intro m
    rcases le_total m ((L - 1) / (1 + gamma)) with hm | hm
    · have hleft :
          (gamma * L + 1) / (1 + gamma) ≤ L - m := by
        rw [← hm_eq]
        linarith
      exact le_trans hleft (le_max_left _ _)
    · have hright :
          (gamma * L + 1) / (1 + gamma) ≤ 1 + gamma * m := by
        rw [← hb_eq]
        nlinarith
      exact le_trans hright (le_max_right _ _)
  · rw [hm_eq, hb_eq, max_self]

end Omega.Conclusion
