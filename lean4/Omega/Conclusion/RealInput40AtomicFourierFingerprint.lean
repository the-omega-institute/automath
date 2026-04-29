import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-realinput40-atomic-fourier-fingerprint`. -/
theorem paper_conclusion_realinput40_atomic_fourier_fingerprint
    (chi : Nat -> Complex) (u z : Complex) :
    (∑ n ∈ Finset.Icc 1 2, (if n = 2 then u * z ^ 2 else 0) * chi n) =
      chi 2 * u * z ^ 2 := by
  simp
  ring

end Omega.Conclusion
