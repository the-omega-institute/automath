import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-rational-functional-calculus-four-rank`. -/
theorem paper_conclusion_window6_rational_functional_calculus_four_rank {F : Type*}
    (rank : F → ℕ) (divStat divBulk : F → Prop)
    (h21 : ∀ f, ¬ divStat f → ¬ divBulk f → rank f = 21)
    (h20 : ∀ f, divStat f → ¬ divBulk f → rank f = 20)
    (h1 : ∀ f, divBulk f → ¬ divStat f → rank f = 1)
    (h0 : ∀ f, divStat f → divBulk f → rank f = 0) :
    ∀ f, rank f = 0 ∨ rank f = 1 ∨ rank f = 20 ∨ rank f = 21 := by
  intro f
  by_cases hstat : divStat f
  · by_cases hbulk : divBulk f
    · exact Or.inl (h0 f hstat hbulk)
    · exact Or.inr (Or.inr (Or.inl (h20 f hstat hbulk)))
  · by_cases hbulk : divBulk f
    · exact Or.inr (Or.inl (h1 f hbulk hstat))
    · exact Or.inr (Or.inr (Or.inr (h21 f hstat hbulk)))

end Omega.Conclusion
