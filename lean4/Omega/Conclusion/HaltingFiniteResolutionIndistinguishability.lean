import Omega.DerivedConsequences.DerivedHaltingResolutionLocalfactorSynchronization

namespace Omega.Conclusion

open _root_.Omega.DerivedConsequences

/-- Paper label: `thm:conclusion-halting-finite-resolution-indistinguishability`. At every finite
resolution `m ≤ L N`, the halting branch with stopping time `N` yields the same truncated
observation as the divergent branch, so the two branches are indistinguishable to any algorithm
that only postcomposes this observation. -/
theorem paper_conclusion_halting_finite_resolution_indistinguishability (L m : ℕ) (hL : 0 < L) :
    ∀ N : ℕ,
      m ≤ L * N →
        derived_halting_resolution_localfactor_synchronization_resolution_observation L m
            (paper_derived_halting_valuation_walsh_ledger_unification_halting_state.haltsAt N) =
          derived_halting_resolution_localfactor_synchronization_resolution_observation L m
            paper_derived_halting_valuation_walsh_ledger_unification_halting_state.diverges := by
  let _ := hL
  intro N hm
  exact derived_halting_resolution_localfactor_synchronization_finite_resolution_blindness L m N hm

end Omega.Conclusion
