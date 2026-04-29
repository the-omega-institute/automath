import Mathlib.Data.Fintype.Card
import Omega.Conclusion.Period3FiberExactMultiplicity
import Omega.Folding.FixedFiberLedgerComplexity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-cnf-npcomplete-periodic`. The period-`3` fiber package
realizes the restricted periodic fiber `x* = (001)^∞` as a full `n`-bit hypercube, while the
fixed-fiber ledger complexity package already supplies witness-based NP membership and the blockwise
Karp reduction from `3`-SAT. -/
theorem paper_conclusion_fiber_cnf_npcomplete_periodic :
    Omega.FoldFibre3SATNPComplete ∧
      (∀ n : ℕ,
        Function.Bijective
            (Omega.Conclusion.Period3FiberExactMultiplicity.period3MiddleProjection n) ∧
          Fintype.card (Fin n → Bool) = 2 ^ n) ∧
      (∀ {n : ℕ} (formula : Omega.FoldFibreThreeCNF (Fin n)),
        Omega.foldFibreFormulaSatisfiable formula ↔
          Omega.foldFibre3SATLanguage (Omega.foldFibreLiftFormula formula)) := by
  refine ⟨Omega.paper_fold_fibre_3sat_np_complete, ?_, ?_⟩
  · intro n
    exact ⟨
      (Omega.Conclusion.Period3FiberExactMultiplicity.paper_conclusion_period3_fiber_hypercube_vc
        n).1,
      (Omega.Conclusion.Period3FiberExactMultiplicity.paper_conclusion_period3_fiber_hypercube_vc
        n).2.2.1⟩
  · intro n formula
    exact (Omega.paper_fold_fibre_3sat_np_complete).2 formula

end Omega.Conclusion
