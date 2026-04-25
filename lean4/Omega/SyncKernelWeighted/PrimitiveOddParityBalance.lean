import Omega.SyncKernelWeighted.PrimitiveOddDiv

namespace Omega.SyncKernelWeighted

open Polynomial
open scoped Polynomial

/-- Paper label: `cor:primitive-odd-parity-balance`. -/
theorem paper_primitive_odd_parity_balance (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n) :
    (Omega.SyncKernelWeighted.primitive_odd_div_poly n).eval (-1 : ℤ) = 0 := by
  have _ : 0 < n := lt_of_lt_of_le (by norm_num) h3
  rcases paper_primitive_odd_div n hn with ⟨_, hdiv⟩
  rcases hdiv with ⟨Q, hQ⟩
  rw [hQ]
  simp

end Omega.SyncKernelWeighted
