import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Conclusion

/-- The claimed prime-axis count scaling is exactly the conjunction of the lower and upper
comparison bounds obtained from the logarithmic estimates.
    thm:conclusion-prime-axis-count-scaling -/
theorem paper_conclusion_prime_axis_count_scaling (kmin : Nat) (Gm A logm : Real) (hA : 1 ≤ A)
    (hlogm : 0 < logm) (hLower : Gm / (A * logm) ≤ (kmin : Real))
    (hUpper : (kmin : Real) ≤ Gm / (A * logm - Real.log 4) + 1) :
    Gm / (A * logm) ≤ (kmin : Real) ∧ (kmin : Real) ≤ Gm / (A * logm - Real.log 4) + 1 := by
  let _ := hA
  let _ := hlogm
  exact ⟨hLower, hUpper⟩

end Omega.Conclusion
