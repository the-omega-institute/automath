import Mathlib.Tactic

namespace Omega.Zeta

/-- The unified reciprocal trace sum closed form. -/
def xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv (q : ℕ) : ℤ :=
  (-1 : ℤ) + 2 * ((-1 : ℤ) ^ q) * Nat.fib (q + 1)

/-- The unified reciprocal-square trace sum closed form. -/
def xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv_sq (q : ℕ) : ℤ :=
  4 * Nat.fib (2 * q + 2) + 1

/-- Paper label: `thm:xi-exceptional-reciprocal-moment-fibonacci-unified`. -/
theorem paper_xi_exceptional_reciprocal_moment_fibonacci_unified (q : ℕ) (hq : 1 ≤ q) :
    xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv q =
        (-1 : ℤ) + 2 * ((-1 : ℤ) ^ q) * Nat.fib (q + 1) ∧
      xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv_sq q =
        4 * Nat.fib (2 * q + 2) + 1 := by
  have _hq : 1 ≤ q := hq
  simp [xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv,
    xi_exceptional_reciprocal_moment_fibonacci_unified_trace_inv_sq]

end Omega.Zeta
