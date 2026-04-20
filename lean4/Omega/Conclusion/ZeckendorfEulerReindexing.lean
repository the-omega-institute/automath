import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

open scoped BigOperators

namespace Omega.Conclusion

/-- Reindex the finite reciprocal-factorial sum along the Zeckendorf range bijection.
    thm:conclusion-zeckendorf-euler-reindexing -/
theorem paper_conclusion_zeckendorf_euler_reindexing (m : ℕ) :
    (∑ x : Omega.X m, ((Nat.factorial (Omega.stableValue x) : ℕ) : ℝ)⁻¹) =
      ∑ i : Fin (Nat.fib (m + 2)), ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹ := by
  have hbij := Omega.X.stableValueFin_bijective m
  rw [show (fun x : Omega.X m => ((Nat.factorial (Omega.stableValue x) : ℕ) : ℝ)⁻¹) =
      (fun i : Fin (Nat.fib (m + 2)) => ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹) ∘
        Omega.stableValueFin from by
        ext x
        simp [Omega.stableValueFin, Omega.X.stableValueFin]]
  exact hbij.sum_comp (fun i : Fin (Nat.fib (m + 2)) => ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹)

end Omega.Conclusion
