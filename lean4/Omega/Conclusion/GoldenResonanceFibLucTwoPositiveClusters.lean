import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedGoldenResonanceDiagonalMultiplierEssentialClusters

open Filter

namespace Omega.Conclusion

noncomputable section

/-- The Fibonacci-side positive cluster constant inherited from the resonance ladder package. -/
def conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint : ℝ :=
  Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point

/-- The Lucas-side positive cluster constant inherited from the resonance ladder package. -/
def conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint : ℝ :=
  Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point

/-- A concrete integer sampling model with Fibonacci and Lucas cluster subsequences. -/
def conclusion_golden_resonance_fib_luc_two_positive_clusters_sequence (n : ℕ) : ℝ :=
  Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_diag n

/-- Paper-facing package for the two distinct positive Fibonacci/Lucas cluster limits. -/
def conclusion_golden_resonance_fib_luc_two_positive_clusters_statement : Prop :=
  0 < conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint ∧
    0 < conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint ∧
    conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint ≠
      conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint ∧
    Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point
      conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint ∧
    Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point
      conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint ∧
    ¬ Tendsto
      conclusion_golden_resonance_fib_luc_two_positive_clusters_sequence atTop (nhds 0) ∧
    (∀ l : ℝ,
      ¬ Tendsto
        conclusion_golden_resonance_fib_luc_two_positive_clusters_sequence atTop (nhds l))

/-- Paper label: `thm:conclusion-golden-resonance-fib-luc-two-positive-clusters`. -/
theorem paper_conclusion_golden_resonance_fib_luc_two_positive_clusters :
    conclusion_golden_resonance_fib_luc_two_positive_clusters_statement := by
  rcases
    Omega.DerivedConsequences.paper_derived_golden_resonance_diagonal_multiplier_essential_clusters
    with ⟨_, _, hFibPos, hLucPos, hNe, hFibCluster, hLucCluster, hNoDecay, hNoScalar, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint] using hFibPos
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint] using hLucPos
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint,
      conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint] using hNe
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_fibPoint] using hFibCluster
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_lucPoint] using hLucCluster
  · simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_sequence,
      Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact]
      using hNoDecay
  · intro l hlim
    have hShift :
        Tendsto
          (fun n =>
            Omega.DerivedConsequences.derived_golden_resonance_diagonal_multiplier_essential_clusters_diag
                n -
              l)
          atTop (nhds 0) := by
      have hConst : Tendsto (fun _ : ℕ => l) atTop (nhds l) := tendsto_const_nhds
      have hSub := hlim.sub hConst
      simpa [conclusion_golden_resonance_fib_luc_two_positive_clusters_sequence] using hSub
    exact hNoScalar l hShift

end

end Omega.Conclusion
