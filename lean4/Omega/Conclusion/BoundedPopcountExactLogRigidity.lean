import Omega.Conclusion.BinarySparsityLogarithmicDeviation

namespace Omega.Conclusion

open BinarySparsityLogarithmicDeviation

/-- Paper label: `cor:conclusion-bounded-popcount-exact-log-rigidity`. Under the repository's
binary-sparsity hypotheses, the logarithmic model is already exact for every `n ≥ 2`, so the
uniform bounded-popcount rigidity constant can be chosen to be `0`. -/
theorem paper_conclusion_bounded_popcount_exact_log_rigidity (delta : Nat → Real) (L : Nat) :
    BinarySparsityHypotheses delta →
      ∃ C : Real,
        ∀ n ≥ 2,
          binaryPopcount n ≤ L →
            |delta n - slope delta * Real.log (n : Real)| ≤ C := by
  intro hdelta
  refine ⟨0, ?_⟩
  intro n hn _hpop
  have hmain : delta n = slope delta * Real.log (n : Real) := hdelta n hn
  rw [hmain]
  norm_num

end Omega.Conclusion
