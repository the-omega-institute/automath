import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Choosing `n = F(2q-2)+1` makes the Cuntz `K₀` modulus `n-1` equal to the Fibonacci
quantity used in the collision package.
    prop:pom-collision-ck-fibonacci-collapse -/
theorem paper_pom_collision_ck_fibonacci_collapse (q : ℕ) (hq : 2 ≤ q) :
    ∃ n : ℕ, n = Nat.fib (2 * q - 2) + 1 ∧ n - 1 = Nat.fib (2 * q - 2) := by
  have _ : 2 ≤ q := hq
  refine ⟨Nat.fib (2 * q - 2) + 1, rfl, ?_⟩
  omega

end Omega.POM
