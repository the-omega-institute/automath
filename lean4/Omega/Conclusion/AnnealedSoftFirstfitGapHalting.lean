import Omega.POM.FractranSoftFirstfitAnnealedBudget
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-annealed-soft-firstfit-gap-halting`. An abstract
trap-augmented soft first-fit gap with nonhalting probability `0` and halting probability at
least `1 - epsilon` is equivalent to halting at the half threshold. -/
theorem paper_conclusion_annealed_soft_firstfit_gap_halting {Machine Input Word : Type}
    (compile : Machine → Input → Word) (halts : Machine → Input → Prop)
    (acceptProb : Word → ℝ) (epsilon : ℝ) (heps_pos : 0 < epsilon)
    (heps_half : epsilon < (1 / 2 : ℝ))
    (hgap : ∀ M x, (¬ halts M x → acceptProb (compile M x) = 0) ∧
      (halts M x → 1 - epsilon ≤ acceptProb (compile M x))) :
    ∀ M x, ((1 / 2 : ℝ) ≤ acceptProb (compile M x) ↔ halts M x) := by
  intro M x
  constructor
  · intro hhalf
    by_contra hnot
    have hzero : acceptProb (compile M x) = 0 := (hgap M x).1 hnot
    linarith
  · intro hhalts
    have hlower : 1 - epsilon ≤ acceptProb (compile M x) := (hgap M x).2 hhalts
    linarith

end Omega.Conclusion
