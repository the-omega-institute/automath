import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-tate-fulltower-rankone-shadow-nonconjugacy`. -/
theorem paper_conclusion_tate_fulltower_rankone_shadow_nonconjugacy
    (compatibleConjugacy : Prop)
    (hcompat : compatibleConjugacy → ∀ n : ℕ, 1 ≤ n → (4 : ℕ) ^ n ≤ (2 : ℕ) ^ n) :
    ¬ compatibleConjugacy := by
  intro h
  have hbad : (4 : ℕ) ^ 1 ≤ (2 : ℕ) ^ 1 := hcompat h 1 (by norm_num)
  norm_num at hbad

end Omega.Conclusion
