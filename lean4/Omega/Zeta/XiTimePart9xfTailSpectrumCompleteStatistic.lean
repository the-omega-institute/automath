import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.CapacityFiniteCompleteness

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part9xf-tail-spectrum-complete-statistic`. -/
theorem paper_xi_time_part9xf_tail_spectrum_complete_statistic {X : Type*} [Fintype X]
    (d : X → ℕ) :
    let h : ℕ → ℕ := fun k => Fintype.card {x : X // d x = k}
    let N : ℕ → ℕ := fun t => Fintype.card {x : X // t ≤ d x}
    let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t
    Omega.Conclusion.FiniteMultiplicityDataEquivalent (X := X) h N C
      (fun q => Finset.sum Finset.univ (fun x => d x ^ q)) := by
  classical
  exact Omega.Conclusion.paper_conclusion_capacity_finite_completeness (X := X) d

end Omega.Zeta
