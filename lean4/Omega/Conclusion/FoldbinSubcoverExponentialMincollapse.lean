import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.GoldenSprtTailExponentChernoffIdentity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-subcover-exponential-mincollapse`. The Fibonacci
distortion seeds give the finite `2^m / F_m` side of the subcover count, and the golden-SPRT tail
identity packages the asymptotic exponential collapse rate governed by `2 / φ^(3/2)`. -/
theorem paper_conclusion_foldbin_subcover_exponential_mincollapse
    (T : ℕ) (hT : 2 ≤ T) :
    Nat.fib 5 < 2 ^ 3 ∧
      Nat.fib 6 < 2 ^ 4 ∧
      Nat.fib 7 < 2 ^ 5 ∧
      Nat.fib 8 < 2 ^ 6 ∧
      goldenSprtTailExponent T =
        goldenSprtChernoffConstant - Real.log (Real.cos (Real.pi / (2 * (T : ℝ)))) / Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact paper_conclusion_golden_sprt_tail_exponent_chernoff_identity T hT

end Omega.Conclusion
