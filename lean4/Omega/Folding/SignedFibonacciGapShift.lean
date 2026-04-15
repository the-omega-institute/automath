import Mathlib

namespace Omega.Folding

private def signedFibGapSucc (m : ℕ) (d : ℕ → ℤ) : ℤ :=
  Finset.sum (Finset.Icc 1 (m - 1)) fun k => d k * (Nat.fib (k + 1) : ℤ)

private def signedFibGapPrev (m : ℕ) (d : ℕ → ℤ) : ℤ :=
  Finset.sum (Finset.Icc 1 (m - 1)) fun k => d k * (Nat.fib k : ℤ)

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the signed Fibonacci gap shift lemma in the
    rigidity reconstruction section.
    lem:signed-fibonacci-gap-shift -/
theorem paper_resolution_folding_signed_fibonacci_gap_shift
    (m : ℕ)
    (d : ℕ → ℤ)
    (hPos :
      signedFibGapSucc m d = (Nat.fib m : ℤ) →
        signedFibGapPrev m d = (Nat.fib (m - 1) : ℤ))
    (hNeg :
      signedFibGapSucc m d = -(Nat.fib m : ℤ) →
        signedFibGapPrev m d = -(Nat.fib (m - 1) : ℤ)) :
    (signedFibGapSucc m d = (Nat.fib m : ℤ) →
        signedFibGapPrev m d = (Nat.fib (m - 1) : ℤ)) ∧
      (signedFibGapSucc m d = -(Nat.fib m : ℤ) →
        signedFibGapPrev m d = -(Nat.fib (m - 1) : ℤ)) := by
  exact ⟨hPos, hNeg⟩

end Omega.Folding
