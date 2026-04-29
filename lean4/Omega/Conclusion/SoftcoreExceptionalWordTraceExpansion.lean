import Omega.Zeta.DynZeta

namespace Omega.Conclusion

open Omega.Zeta

/-- Publication-facing wrapper collecting the concrete trace-expansion ingredients for the
softcore exceptional word package. -/
def conclusion_softcore_exceptional_word_trace_expansion_statement : Prop :=
  (∀ n : ℕ, (allOnesMatrix ^ (n + 1)).trace = (2 : ℤ) ^ (n + 1)) ∧
    (allOnesMatrix.trace = 2 ∧
      Graph.goldenMeanAdjacency.trace = 1 ∧
      (∀ q : ℕ, 2 * (2 ^ q + 1) = 2 ^ (q + 1) + 2)) ∧
    ((allOnesMatrix * allOnesMatrix).trace = 4 ∧
      (allOnesMatrix * Graph.goldenMeanAdjacency).trace = 3 ∧
      (Graph.goldenMeanAdjacency * allOnesMatrix).trace = 3 ∧
      (Graph.goldenMeanAdjacency ^ 2).trace = 3) ∧
    ((Graph.goldenMeanAdjacency ^ 3).trace = 4 ∧
      (allOnesMatrix * Graph.goldenMeanAdjacency ^ 2).trace = 5 ∧
      (allOnesMatrix ^ 2 * Graph.goldenMeanAdjacency).trace = 6 ∧
      (allOnesMatrix ^ 3).trace = 8)

/-- Paper label: `thm:conclusion-softcore-exceptional-word-trace-expansion`. -/
theorem paper_conclusion_softcore_exceptional_word_trace_expansion :
    conclusion_softcore_exceptional_word_trace_expansion_statement := by
  exact ⟨allOnesMatrix_pow_trace, paper_word_trace_m1_package, paper_word_trace_m2_traces,
    paper_word_trace_m3_selected⟩

end Omega.Conclusion
