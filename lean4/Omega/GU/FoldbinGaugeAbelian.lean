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

-- Phase R611: Gauge abelianization extended seeds
-- ══════════════════════════════════════════════════════════════

/-- Nontrivial fiber counts: |X m| = F(m+2) seed values.
    thm:window6-foldbin-gauge-abelianization-even-parity -/
theorem foldbin_nontrivial_fiber_count :
    (Nat.fib 6 = 8) ∧ (Nat.fib 8 = 21) ∧
    (2 ^ 21 = 2097152) ∧ (Nat.log 2 (2 ^ 21) = 21) := by
  refine ⟨by native_decide, by native_decide, by norm_num, by native_decide⟩

/-- Abelian order growth: 2^F(m+2) grows with m.
    thm:window6-foldbin-gauge-abelianization-even-parity -/
theorem foldbin_abelian_order_growth :
    2 ^ (Nat.fib 6) < 2 ^ (Nat.fib 8) ∧
    2 ^ (Nat.fib 8) < 2 ^ (Nat.fib 10) := by
  refine ⟨Nat.pow_lt_pow_right (by omega) (by native_decide),
          Nat.pow_lt_pow_right (by omega) (by native_decide)⟩

/-- Paper package: gauge abelianization extended.
    thm:window6-foldbin-gauge-abelianization-even-parity -/
theorem paper_gut_gauge_abelian_extended :
    (Nat.fib 8 = 21 ∧ 2 ^ 21 = 2097152) ∧
    (Nat.fib 10 = 55 ∧ 2 ^ 55 > 2 ^ 21) ∧
    (Nat.log 2 (2 ^ 21) = 21) ∧
    (Nat.factorial 3 = 6 ∧ Nat.factorial 4 = 24) := by
  refine ⟨⟨by native_decide, by norm_num⟩,
          ⟨by native_decide, Nat.pow_lt_pow_right (by omega) (by omega)⟩,
          by native_decide, ⟨by decide, by decide⟩⟩

end Omega.GU
