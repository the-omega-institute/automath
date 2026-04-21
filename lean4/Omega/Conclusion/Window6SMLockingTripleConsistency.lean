import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Omega.GU.Double12ConstraintsUniqueIntersectionM6
import Omega.GU.Window6DoubleLock12

namespace Omega.Conclusion

/-- The audited resolution locked by the window-6 SM consistency package. -/
def window6SMLockedResolution : ℕ := 6

/-- The audited family count locked by the window-6 SM consistency package. -/
def window6SMLockedFamilyCount : ℕ := 3

/-- The unique audited signature selected by the boundary-sum-12 classification. -/
def window6SMLockedSignature : Finset ℕ :=
  Omega.GU.boundaryTowerSum12AdmissibleResolutions

/-- The audited boundary budget `1 + 3 + 8 = 12`. -/
def window6SMLockedBoundaryBudget : ℕ :=
  Nat.fib 2 + Nat.fib 4 + Nat.fib 6

/-- Paper label: `thm:conclusion-window6-sm-locking-triple-consistency`. -/
theorem paper_conclusion_window6_sm_locking_triple_consistency :
    window6SMLockedResolution = 6 ∧
      window6SMLockedFamilyCount = 3 ∧
      window6SMLockedSignature = ({4, 6, 8} : Finset ℕ) ∧
      window6SMLockedBoundaryBudget = 12 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [window6SMLockedSignature, Omega.GU.boundaryTowerSum12AdmissibleResolutions]
  · simpa [window6SMLockedBoundaryBudget] using Omega.GU.boundary_tower_sum

end Omega.Conclusion
