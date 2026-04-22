import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.HaltingLeyangW1Barrier

namespace Omega.FoldComputability

noncomputable section

/-- The Fourier-moment metric contribution of the `q`-th coefficient, weighted by dyadic decay. -/
def fold_computability_halting_no_uniform_learning_fourier_moment_metric
    (q : ℕ) (a b : ℕ → ℝ) : ℝ :=
  Omega.Folding.dyadicScale q * |a q - b q|

/-- Precision used to isolate the `q_e` coefficient in the halting-threshold argument. -/
def fold_computability_halting_no_uniform_learning_epsilon (q : ℕ → ℕ) (e : ℕ) : ℝ :=
  (Omega.Folding.dyadicScale e / 12) * Omega.Folding.dyadicScale (q e)

/-- Threshold test extracted from the claimed uniform learner. -/
def fold_computability_halting_no_uniform_learning_threshold_decider
    (q : ℕ → ℕ) (learner : ℕ → ℝ → ℕ → ℝ) (N0 : ℝ → ℕ) (e : ℕ) : Bool :=
  decide
    (Omega.Folding.haltingW1Threshold e ≤
      learner
        (N0 (fold_computability_halting_no_uniform_learning_epsilon q e))
        (fold_computability_halting_no_uniform_learning_epsilon q e)
        (q e))

/-- Paper label: `cor:fold-computability-halting-no-uniform-learning`.
If a uniform learner approximates the Fourier-moment metric with a computable schedule `N₀`, then
the `q_e`-th coefficient yields a computable threshold test for the halting predicate. Hence such
a learner contradicts undecidability. -/
theorem paper_fold_computability_halting_no_uniform_learning
    (H : ℕ → Prop) [DecidablePred H] (q : ℕ → ℕ) (S : ℝ) (target : ℕ → ℝ)
    (hS_nonneg : 0 ≤ S) (hS_le_one : S ≤ 1)
    (hMomentFormula :
      ∀ e,
        target (q e) =
          if H e then Omega.Folding.dyadicScale e / (1 + S) else 0)
    (hUndecidable : ¬ ∃ decider : ℕ → Bool, ∀ e, decider e = decide (H e)) :
    ¬ ∃ learner : ℕ → ℝ → ℕ → ℝ, ∃ N0 : ℝ → ℕ,
      ∀ e,
        fold_computability_halting_no_uniform_learning_fourier_moment_metric
            (q e)
            (learner
              (N0 (fold_computability_halting_no_uniform_learning_epsilon q e))
              (fold_computability_halting_no_uniform_learning_epsilon q e))
            target <
          fold_computability_halting_no_uniform_learning_epsilon q e := by
  intro hLearner
  rcases hLearner with ⟨learner, N0, hApprox⟩
  let decider :=
    fold_computability_halting_no_uniform_learning_threshold_decider q learner N0
  have hcorrect : ∀ e, decider e = decide (H e) := by
    intro e
    let ε := fold_computability_halting_no_uniform_learning_epsilon q e
    have hmetric :
        fold_computability_halting_no_uniform_learning_fourier_moment_metric
            (q e)
            (learner (N0 ε) ε) target < ε := by
      simpa [ε] using hApprox e
    have hweighted :
        Omega.Folding.dyadicScale (q e) *
            |learner (N0 ε) ε (q e) - target (q e)| < ε := by
      simpa [fold_computability_halting_no_uniform_learning_fourier_moment_metric] using hmetric
    have hcoeff :
        |learner (N0 ε) ε (q e) - target (q e)| <
          Omega.Folding.dyadicScale e / 12 := by
      have hpos : 0 < Omega.Folding.dyadicScale (q e) :=
        Omega.Folding.dyadicScale_pos (q e)
      have hweighted' :
          |learner (N0 ε) ε (q e) - target (q e)| * Omega.Folding.dyadicScale (q e) <
            (Omega.Folding.dyadicScale e / 12) * Omega.Folding.dyadicScale (q e) := by
        simpa [ε, mul_comm, mul_left_comm, mul_assoc] using hweighted
      exact lt_of_mul_lt_mul_right
        hweighted'
        hpos.le
    by_cases hH : H e
    · have htarget :
          target (q e) = Omega.Folding.dyadicScale e / (1 + S) := by
        simpa [hH] using hMomentFormula e
      have hdenom_pos : 0 < 1 + S := by
        linarith
      have hdenom_le : 1 + S ≤ 2 := by
        linarith
      have htarget_lower : Omega.Folding.dyadicScale e / 2 ≤ target (q e) := by
        rw [htarget]
        have hpos : 0 < Omega.Folding.dyadicScale e := Omega.Folding.dyadicScale_pos e
        have hdiv :
            1 / (2 : ℝ) ≤ 1 / (1 + S) := by
          exact one_div_le_one_div_of_le hdenom_pos hdenom_le
        have := mul_le_mul_of_nonneg_left hdiv (le_of_lt hpos)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      have hlow :
          target (q e) - Omega.Folding.dyadicScale e / 12 <
            learner (N0 ε) ε (q e) := by
        have := (abs_lt.mp hcoeff).1
        linarith
      have hthr : Omega.Folding.haltingW1Threshold e ≤ learner (N0 ε) ε (q e) := by
        unfold Omega.Folding.haltingW1Threshold
        have hpos : 0 < Omega.Folding.dyadicScale e := Omega.Folding.dyadicScale_pos e
        linarith
      simp [decider, fold_computability_halting_no_uniform_learning_threshold_decider, ε, hH,
        hthr]
    · have htarget : target (q e) = 0 := by
        simpa [hH] using hMomentFormula e
      have habs :
          |learner (N0 ε) ε (q e)| < Omega.Folding.dyadicScale e / 12 := by
        simpa [htarget, sub_zero] using hcoeff
      have hsmall : learner (N0 ε) ε (q e) < Omega.Folding.dyadicScale e / 6 := by
        have hpos : 0 < Omega.Folding.dyadicScale e := Omega.Folding.dyadicScale_pos e
        have := (abs_lt.mp habs).2
        linarith
      have hnot : ¬ Omega.Folding.haltingW1Threshold e ≤ learner (N0 ε) ε (q e) := by
        unfold Omega.Folding.haltingW1Threshold
        linarith
      simp [decider, fold_computability_halting_no_uniform_learning_threshold_decider, ε, hH,
        hnot]
  exact hUndecidable ⟨decider, hcorrect⟩

end

end Omega.FoldComputability
