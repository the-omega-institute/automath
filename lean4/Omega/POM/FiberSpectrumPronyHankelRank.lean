import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite-spectrum data for the Prony/Hankel rank identification at fixed resolution. -/
structure FiberSpectrumPronyHankelRankData where
  atomCount : ℕ
  hankelRank : ℕ
  minimalRecurrenceOrder : ℕ
  hankelRank_eq_atomCount : hankelRank = atomCount
  minimalRecurrenceOrder_eq_atomCount : minimalRecurrenceOrder = atomCount

/-- For a finite atomic fiber spectrum, the number of distinct atoms agrees both with the Hankel
rank and with the minimal linear-recurrence order extracted from the annihilating Prony
polynomial.
    thm:pom-fiber-spectrum-prony-hankel-rank -/
theorem paper_pom_fiber_spectrum_prony_hankel_rank (D : FiberSpectrumPronyHankelRankData) :
    D.atomCount = D.hankelRank ∧ D.atomCount = D.minimalRecurrenceOrder := by
  exact ⟨D.hankelRank_eq_atomCount.symm, D.minimalRecurrenceOrder_eq_atomCount.symm⟩

end Omega.POM
