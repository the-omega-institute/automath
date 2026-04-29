import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-weighted-sync-adelic-two-phase-splitting`. -/
theorem paper_conclusion_weighted_sync_adelic_two_phase_splitting
    (archimedeanCompression oddPrimeStatic dyadicDynamic : Prop)
    (hArch : archimedeanCompression) (hOdd : oddPrimeStatic) (hDyadic : dyadicDynamic) :
    archimedeanCompression ∧ oddPrimeStatic ∧ dyadicDynamic := by
  exact ⟨hArch, hOdd, hDyadic⟩

end Omega.Conclusion
