import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing exact optimum for rank-two prime-addressable completion: the lower bound from
the Boolean primeblock torsor barrier matches the explicit primorial upper bound pointwise. -/
theorem paper_conclusion_ranktwo_primeaddressable_exact_primorial_optimum
    (Lpa primorialLog : ℕ → ℝ) (hLower : ∀ r, primorialLog r ≤ Lpa r)
    (hUpper : ∀ r, Lpa r ≤ primorialLog r) : ∀ r, Lpa r = primorialLog r := by
  intro r
  exact le_antisymm (hUpper r) (hLower r)

end Omega.Conclusion
