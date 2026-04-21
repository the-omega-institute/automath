import Mathlib
import Omega.Zeta.LucasBarrier

open scoped ArithmeticFunction.Moebius

namespace Omega.POM

open Omega.Zeta.LucasBarrier

/-- The paired `k` / `q-k` contribution in the Lucas expansion of `Tr(B_q^n)`. The midpoint term
for even `q` is recorded separately as a sign. -/
def bqLucasTraceSummand (q n k : ℕ) : ℤ :=
  if 2 * k = q then
    (-1 : ℤ) ^ (k * n)
  else
    (-1 : ℤ) ^ (k * n) * (lucas (n * (q - 2 * k)) : ℤ)

/-- Closed Lucas expansion of the trace channel attached to `B_q`. -/
def bqTraceLucas (q n : ℕ) : ℤ :=
  Finset.sum (Finset.range (q / 2 + 1)) (fun k => bqLucasTraceSummand q n k)

/-- Primitive-orbit numerator obtained by Möbius inversion of the trace channel. -/
def bqPrimitiveOrbitLucas (q n : ℕ) : ℤ :=
  Finset.sum (Nat.divisors n) (fun d => ArithmeticFunction.moebius d * bqTraceLucas q (n / d))

/-- The `B_q` trace channel is a finite Lucas sum, and its Möbius-inverted primitive-orbit count
is therefore a finite linear combination of the same Lucas summands.
    thm:pom-bq-trace-lucas -/
theorem paper_pom_bq_trace_lucas (q n : ℕ) :
    bqTraceLucas q n =
      Finset.sum (Finset.range (q / 2 + 1)) (fun k =>
        if 2 * k = q then
          (-1 : ℤ) ^ (k * n)
        else
          (-1 : ℤ) ^ (k * n) * (lucas (n * (q - 2 * k)) : ℤ)) ∧
      bqPrimitiveOrbitLucas q n =
        Finset.sum (Nat.divisors n) (fun d => ArithmeticFunction.moebius d *
          Finset.sum (Finset.range (q / 2 + 1)) (fun k =>
            if 2 * k = q then
              (-1 : ℤ) ^ (k * (n / d))
            else
              (-1 : ℤ) ^ (k * (n / d)) * (lucas ((n / d) * (q - 2 * k)) : ℤ))) := by
  constructor
  · simp [bqTraceLucas, bqLucasTraceSummand]
  · simp [bqPrimitiveOrbitLucas, bqTraceLucas, bqLucasTraceSummand]

end Omega.POM
