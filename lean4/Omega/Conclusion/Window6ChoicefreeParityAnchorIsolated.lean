import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-choicefree-parity-anchor-isolated`. -/
theorem paper_conclusion_window6_choicefree_parity_anchor_isolated
    (Delta : ℕ → Finset ℕ) (choiceFreeParity : ℕ → Prop)
    (hchoice :
      ∀ m, m ∈ ({6, 7, 8} : Finset ℕ) →
        (choiceFreeParity m ↔ ∃! d, d ∈ Delta m ∧ d ≠ 0))
    (h6 : Delta 6 = ({0, 34} : Finset ℕ))
    (h7 : Delta 7 = ({0, 55, 89} : Finset ℕ))
    (h8 : Delta 8 = ({0, 89, 144} : Finset ℕ)) :
    choiceFreeParity 6 ∧ ¬ choiceFreeParity 7 ∧ ¬ choiceFreeParity 8 := by
  constructor
  · apply (hchoice 6 (by decide)).2
    refine ⟨34, by simp [h6], ?_⟩
    intro y hy
    simp [h6] at hy
    omega
  · constructor
    · intro hparity
      rcases (hchoice 7 (by decide)).1 hparity with ⟨d, hd, hunique⟩
      have h55 : 55 = d := hunique 55 (by simp [h7])
      have h89 : 89 = d := hunique 89 (by simp [h7])
      omega
    · intro hparity
      rcases (hchoice 8 (by decide)).1 hparity with ⟨d, hd, hunique⟩
      have h89 : 89 = d := hunique 89 (by simp [h8])
      have h144 : 144 = d := hunique 144 (by simp [h8])
      omega

end Omega.Conclusion
