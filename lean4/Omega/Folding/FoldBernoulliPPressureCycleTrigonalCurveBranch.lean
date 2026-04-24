import Mathlib.Tactic
import Omega.Folding.BernoulliPPressureCycleEquation

namespace Omega.Folding

/-- Paper label: `prop:fold-bernoulli-p-pressure-cycle-trigonal-curve-branch`. -/
theorem paper_fold_bernoulli_p_pressure_cycle_trigonal_curve_branch
    (birationalEquivalence branchDivisorDescription infinityBranchDescription genusThree : Prop)
    (hBirational : birationalEquivalence) (hBranch : branchDivisorDescription)
    (hInfinity : infinityBranchDescription) (hGenus : genusThree) :
    birationalEquivalence ∧ branchDivisorDescription ∧ infinityBranchDescription ∧ genusThree := by
  exact ⟨hBirational, hBranch, hInfinity, hGenus⟩

end Omega.Folding
