import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Bin-fold gauge group abelian compression seed values

Fibonacci values, factorial values, and power-of-two cardinalities
for the gauge group abelian visible compression theorem.
-/

namespace Omega.GU

/-- Bin-fold gauge abelian compression seeds.
    thm:gut-foldbin-gauge-abelian-visible-compression-even-audited -/
theorem paper_gut_foldbin_gauge_abelian_compression_seeds :
    (Nat.fib 8 = 21) ∧
    (2 ^ 21 = 2097152) ∧
    (Nat.fib 10 = 55) ∧
    (Nat.fib 12 = 144) ∧
    (Nat.fib 3 = 2 ∧ Nat.factorial 2 = 2 ∧ Nat.log 2 2 = 1) ∧
    (Nat.fib 4 = 3 ∧ Nat.factorial 3 = 6) := by
  refine ⟨by native_decide, by norm_num, by native_decide, by native_decide,
          ⟨by decide, by decide, by native_decide⟩,
          ⟨by decide, by decide⟩⟩

end Omega.GU
