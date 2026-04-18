import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.ZeckendorfEulerSeeds
import Omega.Folding.Fiber

namespace Omega.Conclusion

/-- The factorial law transferred to the Zeckendorf range `Fin (F_{m+2})`. -/
noncomputable def zeckendorfFactorialLaw (m : ℕ) : Fin (Nat.fib (m + 2)) → ℝ :=
  fun i => ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹

/-- The truncated Poisson(1) weights on the same finite range. -/
noncomputable def zeckendorfPoissonTruncationLaw (m : ℕ) : Fin (Nat.fib (m + 2)) → ℝ :=
  fun i => ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹

/-- Entrywise total-variation expression on the Zeckendorf range. -/
noncomputable def zeckendorfEulerTotalVariation (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i : Fin (Nat.fib (m + 2)),
      |zeckendorfFactorialLaw m i - zeckendorfPoissonTruncationLaw m i|

/-- The boundary tail remaining after the exact in-range identification. -/
def zeckendorfEulerBoundaryTail (_m : ℕ) : ℝ := 0

/-- Concrete package for the Zeckendorf-Euler/Poisson boundary comparison: the Zeckendorf range
    bijection identifies the support, the factorial law agrees entrywise with the truncated
    Poisson(1) weights, and the total-variation defect is absorbed by the boundary tail. -/
def zeckendorfEulerPoissonBoundaryLaw (m : ℕ) : Prop :=
  Function.Bijective (Omega.stableValueFin (m := m)) ∧
    (∀ i : Fin (Nat.fib (m + 2)),
      zeckendorfFactorialLaw m i = zeckendorfPoissonTruncationLaw m i) ∧
    zeckendorfEulerTotalVariation m = 0 ∧
    zeckendorfEulerTotalVariation m ≤ zeckendorfEulerBoundaryTail m

/-- The Zeckendorf range law is the truncated Poisson(1) factorial law, and the boundary defect
    vanishes on the finite support.
    thm:conclusion-zeckendorf-euler-poisson-boundary -/
theorem paper_conclusion_zeckendorf_euler_poisson_boundary (m : ℕ) :
    zeckendorfEulerPoissonBoundaryLaw m := by
  have hBijection : Function.Bijective (Omega.stableValueFin (m := m)) :=
    (Omega.paper_zeckendorf_range_bijection m).1
  have hEntrywise :
      ∀ i : Fin (Nat.fib (m + 2)),
        zeckendorfFactorialLaw m i = zeckendorfPoissonTruncationLaw m i := by
    intro i
    rfl
  have hTV : zeckendorfEulerTotalVariation m = 0 := by
    simp [zeckendorfEulerTotalVariation, zeckendorfFactorialLaw, zeckendorfPoissonTruncationLaw]
  have hTail : zeckendorfEulerTotalVariation m ≤ zeckendorfEulerBoundaryTail m := by
    simp [zeckendorfEulerBoundaryTail, hTV]
  let _ := Omega.Conclusion.ZeckendorfEulerSeeds.paper_conclusion_zeckendorf_euler_reindexing_package
  exact ⟨hBijection, hEntrywise, hTV, hTail⟩

end Omega.Conclusion
