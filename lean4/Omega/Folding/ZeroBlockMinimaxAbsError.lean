import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Core.Fib

/-!
# Zero-block minimax absolute error

The optimal finite-memory absolute error under zero-block context is
E_n^(0) = 1/(4·F_{n+3}·F_{n+4}), derived from the Fibonacci prediction state
identity |α_{n-1} - α_n| = 1/(2·F_{n+3}·F_{n+4}).

The key identity is a Cassini-type cross product:
  F_{n+2}·F_{n+3} - F_{n+1}·F_{n+4} = (-1)^{n+1}

which in natural number form (for even n+1, i.e. odd n) becomes:
  F_{n+1}·F_{n+4} + 1 = F_{n+2}·F_{n+3}   (n odd)
and for odd n+1 (even n):
  F_{n+2}·F_{n+3} + 1 = F_{n+1}·F_{n+4}   (n even)

## Paper references

- thm:fold-gauge-anomaly-zero-block-minimax-abs-error
-/

namespace Omega.Folding.ZeroBlockMinimaxAbsError

open Nat in
/-! ## Cross-Fibonacci identity: F_{n+2}·F_{n+3} vs F_{n+1}·F_{n+4} -/

/-- Cross-Fibonacci for even n: F_{n+2}·F_{n+3} + 1 = F_{n+1}·F_{n+4}.
    This is a shifted Cassini identity.
    thm:fold-gauge-anomaly-zero-block-minimax-abs-error -/
theorem cross_fib_even (n : ℕ) (heven : Even n) :
    Nat.fib (n + 2) * Nat.fib (n + 3) + 1 = Nat.fib (n + 1) * Nat.fib (n + 4) := by
  have h3 := Nat.fib_add_two (n := n + 2)
  rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h3
  -- F_{n+4} = F_{n+3} + F_{n+2}
  rw [h3]
  -- Need: F_{n+2}·F_{n+3} + 1 = F_{n+1}·(F_{n+3} + F_{n+2})
  --      = F_{n+1}·F_{n+3} + F_{n+1}·F_{n+2}
  -- Cassini even: F_n·F_{n+2} + 1 = F_{n+1}²
  have hcas := Omega.fib_cassini_even n heven
  -- hcas: F_n·F_{n+2} + 1 = F_{n+1}²
  have h1 := Nat.fib_add_two (n := n)
  -- h1: F_{n+2} = F_{n+1} + F_n
  have h2 := Nat.fib_add_two (n := n + 1)
  rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h2
  -- h2: F_{n+3} = F_{n+1} + F_{n+2}
  nlinarith [sq_nonneg (Nat.fib (n + 1)), sq_nonneg (Nat.fib (n + 2)),
             sq_nonneg (Nat.fib n)]

/-- Cross-Fibonacci for odd n: F_{n+1}·F_{n+4} + 1 = F_{n+2}·F_{n+3}.
    thm:fold-gauge-anomaly-zero-block-minimax-abs-error -/
theorem cross_fib_odd (n : ℕ) (hodd : ¬ Even n) :
    Nat.fib (n + 1) * Nat.fib (n + 4) + 1 = Nat.fib (n + 2) * Nat.fib (n + 3) := by
  have h3 := Nat.fib_add_two (n := n + 2)
  rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h3
  have hcas := Omega.fib_cassini_odd n hodd
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h2
  nlinarith [sq_nonneg (Nat.fib (n + 1)), sq_nonneg (Nat.fib (n + 2)),
             sq_nonneg (Nat.fib n)]

/-! ## Difference of consecutive prediction rates -/

/-- The absolute difference |α_{n-1} - α_n| expressed as a natural number
    cross-product identity. For the epsilon-machine prediction states,
    α_k = F_{k+2}/(2·F_{k+4}), so:
    |α_{n-1} - α_n| = |F_{n+1}·F_{n+4} - F_{n+2}·F_{n+3}| / (2·F_{n+3}·F_{n+4})
                     = 1 / (2·F_{n+3}·F_{n+4}).

    This seed verifies the numerator identity for small n.
    thm:fold-gauge-anomaly-zero-block-minimax-abs-error -/
theorem cross_fib_diff_seeds :
    -- n=2 (even): F_4·F_5 + 1 = F_3·F_6
    (Nat.fib 4 * Nat.fib 5 + 1 = Nat.fib 3 * Nat.fib 6) ∧
    -- n=3 (odd): F_4·F_7 + 1 = F_5·F_6
    (Nat.fib 4 * Nat.fib 7 + 1 = Nat.fib 5 * Nat.fib 6) ∧
    -- n=4 (even): F_6·F_7 + 1 = F_5·F_8
    (Nat.fib 6 * Nat.fib 7 + 1 = Nat.fib 5 * Nat.fib 8) ∧
    -- n=5 (odd): F_6·F_9 + 1 = F_7·F_8
    (Nat.fib 6 * Nat.fib 9 + 1 = Nat.fib 7 * Nat.fib 8) := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## Minimax error formula: E_n = 1/(4·F_{n+3}·F_{n+4}) -/

/-- The denominator 4·F_{n+3}·F_{n+4} for small n values:
    n=2: 4·F_5·F_6 = 4·5·8 = 160
    n=3: 4·F_6·F_7 = 4·8·13 = 416
    n=4: 4·F_7·F_8 = 4·13·21 = 1092
    thm:fold-gauge-anomaly-zero-block-minimax-abs-error -/
theorem minimax_denominator_seeds :
    (4 * Nat.fib 5 * Nat.fib 6 = 160) ∧
    (4 * Nat.fib 6 * Nat.fib 7 = 416) ∧
    (4 * Nat.fib 7 * Nat.fib 8 = 1092) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Combined paper theorem: the cross-Fibonacci identity (numerator = 1)
    and denominator seeds for the minimax error formula.
    thm:fold-gauge-anomaly-zero-block-minimax-abs-error -/
theorem paper_fold_zero_block_minimax_abs_error :
    -- Cross-Fibonacci seeds (numerator identity)
    (Nat.fib 4 * Nat.fib 5 + 1 = Nat.fib 3 * Nat.fib 6) ∧
    (Nat.fib 4 * Nat.fib 7 + 1 = Nat.fib 5 * Nat.fib 6) ∧
    -- Denominator seeds
    (4 * Nat.fib 5 * Nat.fib 6 = 160) ∧
    (4 * Nat.fib 6 * Nat.fib 7 = 416) ∧
    -- General cross-Fibonacci identity (even case, using Cassini)
    (∀ n : ℕ, Even n → Nat.fib (n + 2) * Nat.fib (n + 3) + 1 =
      Nat.fib (n + 1) * Nat.fib (n + 4)) ∧
    -- General cross-Fibonacci identity (odd case, using Cassini)
    (∀ n : ℕ, ¬ Even n → Nat.fib (n + 1) * Nat.fib (n + 4) + 1 =
      Nat.fib (n + 2) * Nat.fib (n + 3)) := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
         cross_fib_even, cross_fib_odd⟩

end Omega.Folding.ZeroBlockMinimaxAbsError
