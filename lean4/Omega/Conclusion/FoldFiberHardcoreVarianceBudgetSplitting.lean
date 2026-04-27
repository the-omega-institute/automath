import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-fiber-hardcore-variance-budget-splitting`. -/
theorem paper_conclusion_fold_fiber_hardcore_variance_budget_splitting
    (m : Nat) (p within between total : Rat) (hbinom : total = (m : Rat) * p * (1 - p))
    (hvariance : total = within + between) :
    (m : Rat) * p * (1 - p) = within + between := by
  rw [← hbinom, hvariance]

end Omega.Conclusion
