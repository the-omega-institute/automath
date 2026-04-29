import Omega.Conclusion.MaxfiberHomotopyVisibilityDensity

namespace Omega.Conclusion

/-- Concrete data token for the maxfiber uniphase `mod 6` law.  The visibility predicates below
are derived from the existing noncontractible fiber-count interface. -/
structure conclusion_maxfiber_uniphase_mod6_law_data where

namespace conclusion_maxfiber_uniphase_mod6_law_data

/-- The max-visible branch: the `0/4 mod 6` phase together with equality to the main fiber. -/
def maxVisible (_D : conclusion_maxfiber_uniphase_mod6_law_data) (m : ℕ) : Prop :=
  (m % 6 = 0 ∨ m % 6 = 4) ∧
    noncontractibleFiberCount m = noncontractibleMainFiberCount m

/-- The all-max-visible branch records the same concrete certificates in the opposite order. -/
def allMaxVisible (_D : conclusion_maxfiber_uniphase_mod6_law_data) (m : ℕ) : Prop :=
  noncontractibleFiberCount m = noncontractibleMainFiberCount m ∧
    (m % 6 = 0 ∨ m % 6 = 4)

end conclusion_maxfiber_uniphase_mod6_law_data

/-- Paper label: `thm:conclusion-maxfiber-uniphase-mod6-law`. -/
theorem paper_conclusion_maxfiber_uniphase_mod6_law
    (D : conclusion_maxfiber_uniphase_mod6_law_data) :
    ∀ m : ℕ, 17 ≤ m →
      (D.maxVisible m ↔ D.allMaxVisible m) ∧
        (D.maxVisible m ↔ m % 6 = 0 ∨ m % 6 = 4) := by
  intro m hm
  have hphase :=
    (paper_conclusion_maxfiber_homotopy_visibility_density True trivial).1 m hm
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  · constructor
    · intro h
      exact h.1
    · intro hmod
      exact ⟨hmod, hphase hmod⟩

end Omega.Conclusion
