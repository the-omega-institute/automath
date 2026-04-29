import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete cost-model package for the conclusion-slice impossibility wrapper. A global
optimizer would itself be the forbidden uniform exact additive approximation. -/
structure conclusion_slice_computable_global_optimal_synthesizer_impossible_package where
  conclusion_slice_computable_global_optimal_synthesizer_impossible_Instance : Type
  conclusion_slice_computable_global_optimal_synthesizer_impossible_Candidate : Type
  conclusion_slice_computable_global_optimal_synthesizer_impossible_cost :
    conclusion_slice_computable_global_optimal_synthesizer_impossible_Instance →
      conclusion_slice_computable_global_optimal_synthesizer_impossible_Candidate → ℕ
  conclusion_slice_computable_global_optimal_synthesizer_impossible_noUniformApproximation :
    ¬ ∃ synth :
        conclusion_slice_computable_global_optimal_synthesizer_impossible_Instance →
          conclusion_slice_computable_global_optimal_synthesizer_impossible_Candidate,
      ∀ x y,
        conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x (synth x) ≤
          conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x y

namespace conclusion_slice_computable_global_optimal_synthesizer_impossible_package

/-- Existence of a total global optimal synthesizer for every slice instance. -/
def existsGlobalOptimal
    (P : conclusion_slice_computable_global_optimal_synthesizer_impossible_package) : Prop :=
  ∃ synth :
      P.conclusion_slice_computable_global_optimal_synthesizer_impossible_Instance →
        P.conclusion_slice_computable_global_optimal_synthesizer_impossible_Candidate,
    ∀ x y,
      P.conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x (synth x) ≤
        P.conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x y

/-- The uniform exact additive approximation induced by such a synthesizer. -/
def uniformExactApproximation
    (P : conclusion_slice_computable_global_optimal_synthesizer_impossible_package) : Prop :=
  ∃ synth :
      P.conclusion_slice_computable_global_optimal_synthesizer_impossible_Instance →
        P.conclusion_slice_computable_global_optimal_synthesizer_impossible_Candidate,
    ∀ x y,
      P.conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x (synth x) ≤
        P.conclusion_slice_computable_global_optimal_synthesizer_impossible_cost x y

theorem conclusion_slice_computable_global_optimal_synthesizer_impossible_global_to_uniform
    (P : conclusion_slice_computable_global_optimal_synthesizer_impossible_package) :
    P.existsGlobalOptimal → P.uniformExactApproximation := by
  intro h
  simpa [existsGlobalOptimal, uniformExactApproximation] using h

end conclusion_slice_computable_global_optimal_synthesizer_impossible_package

/-- Paper label: `thm:conclusion-slice-computable-global-optimal-synthesizer-impossible`. -/
theorem paper_conclusion_slice_computable_global_optimal_synthesizer_impossible
    (P : conclusion_slice_computable_global_optimal_synthesizer_impossible_package) :
    Not P.existsGlobalOptimal := by
  intro hglobal
  exact
    P.conclusion_slice_computable_global_optimal_synthesizer_impossible_noUniformApproximation
      (P.conclusion_slice_computable_global_optimal_synthesizer_impossible_global_to_uniform hglobal)

end Omega.Conclusion
