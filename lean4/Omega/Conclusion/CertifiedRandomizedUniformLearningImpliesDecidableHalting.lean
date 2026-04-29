import Mathlib.Tactic
import Omega.FoldComputability.HaltingNoUniformLearning

namespace Omega.Conclusion

noncomputable section

open Omega.FoldComputability

/-- Bounded random seeds available to the certified learner at precision `ε`. -/
def conclusion_certified_randomized_uniform_learning_implies_decidable_halting_seedBound
    (seedBudget : ℝ → ℕ) (ε : ℝ) : Prop :=
  0 < seedBudget ε

/-- Certified finite-randomness learning hypothesis: every bounded seed passes the deterministic
certificate, so enumerating the seed set and choosing seed `0` yields a deterministic learner. -/
def conclusion_certified_randomized_uniform_learning_implies_decidable_halting_randomizedLearns
    (q : ℕ → ℕ) (target : ℕ → ℝ)
    (randomizedLearner : ℕ → ℝ → ℕ → ℕ → ℝ)
    (seedBudget : ℝ → ℕ) (N0 : ℝ → ℕ) : Prop :=
  (∀ ε, conclusion_certified_randomized_uniform_learning_implies_decidable_halting_seedBound
    seedBudget ε) ∧
    ∀ e,
      let ε := fold_computability_halting_no_uniform_learning_epsilon q e
      ∀ seed, seed < seedBudget ε →
        fold_computability_halting_no_uniform_learning_fourier_moment_metric
            (q e)
            (randomizedLearner (N0 ε) ε seed)
            target <
          ε

/-- Target-prefixed conclusion: a certified finite-randomness uniform learner would derandomize
to the deterministic learner forbidden by the halting obstruction theorem. -/
def conclusion_certified_randomized_uniform_learning_implies_decidable_halting_statement : Prop :=
  ∀ (H : ℕ → Prop) [DecidablePred H] (q : ℕ → ℕ) (S : ℝ) (target : ℕ → ℝ),
    0 ≤ S →
    S ≤ 1 →
    (∀ e,
      target (q e) =
        if H e then Omega.Folding.dyadicScale e / (1 + S) else 0) →
    (¬ ∃ decider : ℕ → Bool, ∀ e, decider e = decide (H e)) →
      ¬ ∃ randomizedLearner : ℕ → ℝ → ℕ → ℕ → ℝ, ∃ seedBudget : ℝ → ℕ,
        ∃ N0 : ℝ → ℕ,
          conclusion_certified_randomized_uniform_learning_implies_decidable_halting_randomizedLearns
            q target randomizedLearner seedBudget N0

/-- Paper label:
`thm:conclusion-certified-randomized-uniform-learning-implies-decidable-halting`. -/
theorem paper_conclusion_certified_randomized_uniform_learning_implies_decidable_halting :
    conclusion_certified_randomized_uniform_learning_implies_decidable_halting_statement := by
  intro H hDec q S target hS_nonneg hS_le_one hMomentFormula hUndecidable hRandomized
  rcases hRandomized with ⟨randomizedLearner, seedBudget, N0, hCertified⟩
  rcases hCertified with ⟨hSeedBound, hCertifiedApprox⟩
  apply
    (paper_fold_computability_halting_no_uniform_learning H q S target hS_nonneg hS_le_one
      hMomentFormula hUndecidable)
  refine ⟨fun N ε q => randomizedLearner N ε 0 q, N0, ?_⟩
  intro e
  let ε := fold_computability_halting_no_uniform_learning_epsilon q e
  exact hCertifiedApprox e 0 (hSeedBound ε)

end

end Omega.Conclusion
