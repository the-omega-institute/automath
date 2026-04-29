import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete two-letter alphabet for the conclusion softcore word-trace model. -/
inductive conclusion_softcore_wordtrace_fibonacci_factorization_letter where
  | conclusion_softcore_wordtrace_fibonacci_factorization_K
  | conclusion_softcore_wordtrace_fibonacci_factorization_J
  deriving DecidableEq, Repr

open conclusion_softcore_wordtrace_fibonacci_factorization_letter

/-- A word contains at least one `J` letter. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_hasJ
    (w : List conclusion_softcore_wordtrace_fibonacci_factorization_letter) : Prop :=
  conclusion_softcore_wordtrace_fibonacci_factorization_J ∈ w

/-- Prefix scanner for the lengths of consecutive `K`-blocks between `J` letters. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom (run : ℕ) :
    List conclusion_softcore_wordtrace_fibonacci_factorization_letter → List ℕ
  | [] => [run]
  | conclusion_softcore_wordtrace_fibonacci_factorization_K :: w =>
      conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom (run + 1) w
  | conclusion_softcore_wordtrace_fibonacci_factorization_J :: w =>
      run :: conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom 0 w

/-- The block decomposition of a non-pure softcore word. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_decompose
    (w : List conclusion_softcore_wordtrace_fibonacci_factorization_letter)
    (_hJ : conclusion_softcore_wordtrace_fibonacci_factorization_hasJ w) : List ℕ :=
  conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom 0 w

/-- Fibonacci product attached to a list of `K`-block lengths. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct :
    List ℕ → ℕ
  | [] => 1
  | b :: bs =>
      Nat.fib (b + 1) *
        conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct bs

/-- Direct recursive trace model: each completed `K`-block contributes its Fibonacci factor. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom (run : ℕ) :
    List conclusion_softcore_wordtrace_fibonacci_factorization_letter → ℕ
  | [] => Nat.fib (run + 1)
  | conclusion_softcore_wordtrace_fibonacci_factorization_K :: w =>
      conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom (run + 1) w
  | conclusion_softcore_wordtrace_fibonacci_factorization_J :: w =>
      Nat.fib (run + 1) *
        conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom 0 w

/-- Trace of a concrete K/J softcore word. -/
def conclusion_softcore_wordtrace_fibonacci_factorization_trace
    (w : List conclusion_softcore_wordtrace_fibonacci_factorization_letter) : ℕ :=
  conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom 0 w

lemma conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom_eq_factorProduct
    (run : ℕ) (w : List conclusion_softcore_wordtrace_fibonacci_factorization_letter) :
    conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom run w =
      conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct
        (conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom run w) := by
  induction w generalizing run with
  | nil =>
      simp [conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom,
        conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom,
        conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct]
  | cons a w ih =>
      cases a <;>
        simp [conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom,
          conclusion_softcore_wordtrace_fibonacci_factorization_decomposeFrom,
          conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct, ih]

/-- Paper label: `prop:conclusion-softcore-wordtrace-fibonacci-factorization`. -/
theorem paper_conclusion_softcore_wordtrace_fibonacci_factorization
    (w : List conclusion_softcore_wordtrace_fibonacci_factorization_letter)
    (hJ : conclusion_softcore_wordtrace_fibonacci_factorization_hasJ w) :
    conclusion_softcore_wordtrace_fibonacci_factorization_trace w =
      conclusion_softcore_wordtrace_fibonacci_factorization_factorProduct
        (conclusion_softcore_wordtrace_fibonacci_factorization_decompose w hJ) := by
  simpa [conclusion_softcore_wordtrace_fibonacci_factorization_trace,
    conclusion_softcore_wordtrace_fibonacci_factorization_decompose] using
    conclusion_softcore_wordtrace_fibonacci_factorization_traceFrom_eq_factorProduct 0 w

end Omega.Conclusion
