import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part69c-minsector-fib-extension-pigeonhole-cutoff`. -/
theorem paper_xi_time_part69c_minsector_fib_extension_pigeonhole_cutoff :
    (∀ m ∈ ({6, 8, 10, 12, 14, 16, 18, 20, 22} : Finset ℕ),
        Nat.fib (m + 2) * Nat.fib (m / 2) ≤ 2 ^ m) ∧
      2 ^ 24 < Nat.fib 26 * Nat.fib 12 := by
  native_decide

end Omega.Zeta
