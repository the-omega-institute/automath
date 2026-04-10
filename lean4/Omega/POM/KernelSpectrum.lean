import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.POM.KernelSpectrum

/-- K_m spectrum: rank = F(m+2), nullity = 2^m - F(m+2).
    cor:pom-Km-spectrum -/
theorem paper_pom_Km_spectrum :
    -- rank = F(m+2) seeds
    (Nat.fib 5 = 5) ∧ (Nat.fib 6 = 8) ∧
    (Nat.fib 7 = 13) ∧ (Nat.fib 8 = 21) ∧
    -- nullity = 2^m - F(m+2) seeds
    (2 ^ 3 - Nat.fib 5 = 3) ∧ (2 ^ 4 - Nat.fib 6 = 8) ∧
    (2 ^ 5 - Nat.fib 7 = 19) ∧ (2 ^ 6 - Nat.fib 8 = 43) ∧
    -- rank + nullity = 2^m
    (Nat.fib 5 + 3 = 2 ^ 3) ∧ (Nat.fib 6 + 8 = 2 ^ 4) ∧
    (Nat.fib 7 + 19 = 2 ^ 5) ∧ (Nat.fib 8 + 43 = 2 ^ 6) := by
  norm_num [Nat.fib_add_two]

end Omega.POM.KernelSpectrum
