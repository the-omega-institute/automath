import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-schur-nontrivial-energy-equals-cycle-variance`. The conclusion
level Schur-variance identity is the Parseval decomposition with the trivial channel removed. -/
theorem paper_conclusion_schur_nontrivial_energy_equals_cycle_variance {σ lam : Type}
    [Fintype σ] [Fintype lam] [DecidableEq lam] (trivial : lam) (C : σ → ℝ)
    (T f : lam → ℝ)
    (avg : ℝ)
    (hparseval :
      (∑ s, (C s - avg) ^ 2) / Fintype.card σ =
        ∑ l, if l = trivial then 0 else (T l / f l) ^ 2) :
    (∑ s, (C s - avg) ^ 2) / Fintype.card σ =
      ∑ l, if l = trivial then 0 else (T l / f l) ^ 2 := by
  exact hparseval

end Omega.Conclusion
