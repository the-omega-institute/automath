import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Omega.SyncKernelWeighted.RealInput40TraceRecurrence

namespace Omega.SyncKernelWeighted

open scoped ArithmeticFunction.Moebius BigOperators

/-- Paper label: `cor:real-input-40-primitive-lucas`.
Substituting the Lucas-square closed form for the real-input-40 trace into the standard Möbius
primitive-count formula gives the displayed divisor sum; the later cancellation of the constant and
sign terms is deferred to the downstream simplified corollary. -/
theorem paper_real_input_40_primitive_lucas : ∀ n : ℕ,
    (1 / (n : ℚ)) * Finset.sum n.divisors
      (fun d => (ArithmeticFunction.moebius d : ℚ) * (realInput40TraceSequence (n / d) : ℚ)) =
    (1 / (n : ℚ)) * Finset.sum n.divisors
      (fun d => (ArithmeticFunction.moebius d : ℚ) *
        (((Omega.lucasNum (n / d) : ℚ) ^ 2) +
          (-1 : ℚ) ^ (n / d) * ((Omega.lucasNum (n / d) : ℚ) + 1) + 2)) := by
  intro n
  refine congrArg (fun t : ℚ => (1 / (n : ℚ)) * t) ?_
  refine Finset.sum_congr rfl ?_
  intro d hd
  norm_num [realInput40TraceSequence]

end Omega.SyncKernelWeighted
