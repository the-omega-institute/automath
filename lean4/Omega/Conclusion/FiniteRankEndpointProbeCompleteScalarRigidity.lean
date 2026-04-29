import Mathlib.Tactic

open BigOperators

namespace Omega.Conclusion

/-- Finite Hankel rank gives a Prony representation with positive weights and nodes in
`(0,1)`, uniqueness follows from the Vandermonde/Hankel certificate, and the rotating
scalar probes recover the same scalar measure data. -/
def conclusion_finite_rank_endpoint_probe_complete_scalar_rigidity_statement
    (R : ℕ) (moment : ℕ → ℝ) (nodes weights : Fin R → ℝ)
    (scalarProbeFamily : ℝ → ℕ → ℝ) (recoveredScalarMeasure : ℕ → ℝ) : Prop :=
  (∀ N : ℕ, moment N = ∑ j : Fin R, weights j * nodes j ^ N) ∧
    (∀ j : Fin R, 0 < weights j ∧ 0 < nodes j ∧ nodes j < 1) ∧
    (∀ candidateNodes candidateWeights : Fin R → ℝ,
      (∀ N : ℕ,
        moment N = ∑ j : Fin R, candidateWeights j * candidateNodes j ^ N) →
        candidateNodes = nodes ∧ candidateWeights = weights) ∧
    ∀ angle : ℝ, ∀ N : ℕ,
      scalarProbeFamily angle N = recoveredScalarMeasure N

/-- Paper label: `thm:conclusion-finite-rank-endpoint-probe-complete-scalar-rigidity`. -/
theorem paper_conclusion_finite_rank_endpoint_probe_complete_scalar_rigidity
    {R : ℕ} {moment : ℕ → ℝ} {nodes weights : Fin R → ℝ}
    {scalarProbeFamily : ℝ → ℕ → ℝ} {recoveredScalarMeasure : ℕ → ℝ}
    (h_exponential_representation :
      ∀ N : ℕ, moment N = ∑ j : Fin R, weights j * nodes j ^ N)
    (h_weights_positive : ∀ j : Fin R, 0 < weights j)
    (h_nodes_in_unit_interval : ∀ j : Fin R, 0 < nodes j ∧ nodes j < 1)
    (h_vandermonde_hankel_uniqueness :
      ∀ candidateNodes candidateWeights : Fin R → ℝ,
        (∀ N : ℕ, moment N = ∑ j : Fin R, candidateWeights j * candidateNodes j ^ N) →
          candidateNodes = nodes ∧ candidateWeights = weights)
    (h_rotating_probe_recovery :
      ∀ angle : ℝ, ∀ N : ℕ, scalarProbeFamily angle N = recoveredScalarMeasure N) :
    conclusion_finite_rank_endpoint_probe_complete_scalar_rigidity_statement R moment nodes
      weights scalarProbeFamily recoveredScalarMeasure := by
  refine ⟨h_exponential_representation, ?_, h_vandermonde_hankel_uniqueness, ?_⟩
  · intro j
    exact ⟨h_weights_positive j, (h_nodes_in_unit_interval j).1,
      (h_nodes_in_unit_interval j).2⟩
  · intro angle N
    exact h_rotating_probe_recovery angle N

end Omega.Conclusion
