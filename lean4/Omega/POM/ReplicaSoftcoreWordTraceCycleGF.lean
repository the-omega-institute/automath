import Mathlib

namespace Omega.POM

open Polynomial
open scoped BigOperators

noncomputable section

/-- The Fibonacci block weight `f_s = F_{s+3}^q` from the replica-softcore word trace expansion. -/
def pomReplicaSoftcoreWordTraceCoeff (q s : ℕ) : ℚ :=
  (Nat.fib (s + 3) : ℚ) ^ q

/-- Truncated ordinary generating function `G_q(z) = Σ_{s ≤ N} f_s z^s`. -/
def pomReplicaSoftcoreWordTraceBaseGFTrunc (q N : ℕ) : Polynomial ℚ :=
  Finset.sum (Finset.range (N + 1)) fun s =>
    C (pomReplicaSoftcoreWordTraceCoeff q s) * X ^ s

/-- Truncated derivative kernel `Σ_{s ≤ N} (s+1) f_s z^s`, the algebraic core of the cycle-word
generating function. -/
def pomReplicaSoftcoreWordTraceCycleGFTrunc (q N : ℕ) : Polynomial ℚ :=
  Finset.sum (Finset.range (N + 1)) fun s =>
    C ((((s + 1 : ℕ) : ℚ) * pomReplicaSoftcoreWordTraceCoeff q s)) * X ^ s

/-- Finite-level formal-power-series identity underlying the cycle-word generating function:
`Σ (s+1) f_s z^s = d/dz (z G_q(z))`. The full paper statement is the corresponding infinite
ordinary generating function obtained from these compatible truncations.
    thm:pom-replica-softcore-word-trace-cycle-gf -/
theorem paper_pom_replica_softcore_word_trace_cycle_gf (q N : ℕ) :
    pomReplicaSoftcoreWordTraceCycleGFTrunc q N =
      derivative (X * pomReplicaSoftcoreWordTraceBaseGFTrunc q N) := by
  symm
  calc
    derivative (X * pomReplicaSoftcoreWordTraceBaseGFTrunc q N)
        = derivative
            (Finset.sum (Finset.range (N + 1)) fun s =>
              C (pomReplicaSoftcoreWordTraceCoeff q s) * X ^ (s + 1)) := by
            congr 1
            rw [pomReplicaSoftcoreWordTraceBaseGFTrunc, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro s hs
            calc
              X * (C (pomReplicaSoftcoreWordTraceCoeff q s) * X ^ s)
                  = (X * C (pomReplicaSoftcoreWordTraceCoeff q s)) * X ^ s := by
                      rw [mul_assoc]
              _ = (C (pomReplicaSoftcoreWordTraceCoeff q s) * X) * X ^ s := by
                    rw [mul_comm X (C (pomReplicaSoftcoreWordTraceCoeff q s))]
              _ = C (pomReplicaSoftcoreWordTraceCoeff q s) * (X * X ^ s) := by
                    rw [← mul_assoc]
              _ = C (pomReplicaSoftcoreWordTraceCoeff q s) * X ^ (s + 1) := by
                    congr 1
                    rw [(pow_succ' X s).symm]
    _ = Finset.sum (Finset.range (N + 1)) fun s =>
          C ((((s + 1 : ℕ) : ℚ) * pomReplicaSoftcoreWordTraceCoeff q s)) * X ^ s := by
          rw [derivative_sum]
          refine Finset.sum_congr rfl ?_
          intro s hs
          simpa [pomReplicaSoftcoreWordTraceCoeff, mul_assoc, mul_left_comm, mul_comm] using
            (Polynomial.derivative_C_mul_X_pow (pomReplicaSoftcoreWordTraceCoeff q s) (s + 1))
    _ = pomReplicaSoftcoreWordTraceCycleGFTrunc q N := by
          simp [pomReplicaSoftcoreWordTraceCycleGFTrunc]

end
end Omega.POM
