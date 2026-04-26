import Mathlib.Tactic
import Omega.POM.MaxFiberEvenMajorityVote

namespace Omega.POM

/-- The majority-vote likelihood ratio depends only on the count statistic `S_n`, and distinct
count values induce distinct ratios. This packages the minimal-sufficiency content together with
the single-sample closed form. -/
def pom_max_fiber_hidden_bit_minimal_sufficient_statement (k n : Nat) : Prop :=
  (∀ s : Nat,
    pom_max_fiber_even_majority_vote_logLikelihoodRatio k n s =
      (((2 : ℤ) * s - n : ℤ) : ℝ) *
        Real.log (pom_max_fiber_even_majority_vote_oddsRatio k)) ∧
    (∀ s t : Nat,
      pom_max_fiber_even_majority_vote_logLikelihoodRatio k n s =
          pom_max_fiber_even_majority_vote_logLikelihoodRatio k n t ↔
        s = t) ∧
    (pom_max_fiber_even_majority_vote_logLikelihoodRatio k 1 1 =
      Real.log (pom_max_fiber_even_majority_vote_oddsRatio k)) ∧
    (pom_max_fiber_even_majority_vote_logLikelihoodRatio k 1 0 =
      -Real.log (pom_max_fiber_even_majority_vote_oddsRatio k))

theorem paper_pom_max_fiber_hidden_bit_minimal_sufficient
    (k n : Nat) : pom_max_fiber_hidden_bit_minimal_sufficient_statement k n := by
  rcases paper_pom_max_fiber_even_majority_vote k n with ⟨_, _, hlog_pos, _, _⟩
  have hlog_ne : Real.log (pom_max_fiber_even_majority_vote_oddsRatio k) ≠ 0 :=
    ne_of_gt hlog_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    rfl
  · intro s t
    constructor
    · intro hEq
      rw [pom_max_fiber_even_majority_vote_logLikelihoodRatio,
        pom_max_fiber_even_majority_vote_logLikelihoodRatio] at hEq
      have hcoeff :
          (((2 : ℤ) * s - n : ℤ) : ℝ) = (((2 : ℤ) * t - n : ℤ) : ℝ) := by
        exact (mul_right_inj' hlog_ne).mp (by simpa [mul_comm] using hEq)
      have hint : (2 : ℤ) * s - n = (2 : ℤ) * t - n := by
        exact_mod_cast hcoeff
      omega
    · intro hst
      subst hst
      rfl
  · simp [pom_max_fiber_even_majority_vote_logLikelihoodRatio]
  · simp [pom_max_fiber_even_majority_vote_logLikelihoodRatio]

end Omega.POM
