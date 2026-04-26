import Omega.GU.MinSectorBudget

namespace Omega.GU

/-- Paper-facing package of the audited even-window Fibonacci identities for the minimum
degeneracy sector.
    thm:fold-bin-min-degeneracy-fib-audited -/
theorem paper_fold_bin_min_degeneracy_fib_audited :
    (2 = Nat.fib (6 / 2) ∧ 8 = Nat.fib 6) ∧
      (3 = Nat.fib (8 / 2) ∧ 21 = Nat.fib 8) ∧
      (5 = Nat.fib (10 / 2) ∧ 55 = Nat.fib 10) ∧
      (8 = Nat.fib (12 / 2) ∧ 144 = Nat.fib 12) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by simpa using Omega.GU.MinSectorBudget.dmin_values.1.symm,
      by simpa using Omega.GU.MinSectorBudget.sector_sizes.1.symm⟩
  · exact ⟨by simpa using Omega.GU.MinSectorBudget.dmin_values.2.1.symm,
      by simpa using Omega.GU.MinSectorBudget.sector_sizes.2.1.symm⟩
  · exact ⟨by simpa using Omega.GU.MinSectorBudget.dmin_values.2.2.1.symm,
      by simpa using Omega.GU.MinSectorBudget.sector_sizes.2.2.1.symm⟩
  · exact ⟨by simpa using Omega.GU.MinSectorBudget.dmin_values.2.2.2.symm,
      by simpa using Omega.GU.MinSectorBudget.sector_sizes.2.2.2.symm⟩

end Omega.GU
