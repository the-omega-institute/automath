import Omega.POM.MaxFiberEvenMajorityVote

namespace Omega.POM

theorem paper_pom_max_fiber_even_single_sample_map (k : Nat) :
    pom_max_fiber_even_majority_vote_logLikelihoodRatio k 1 1 > 0 ∧
      pom_max_fiber_even_majority_vote_logLikelihoodRatio k 1 0 < 0 ∧
      pom_max_fiber_even_majority_vote_successProb k =
        (Nat.fib (k + 3) : ℝ) / (Nat.fib (k + 4) : ℝ) ∧
      1 - pom_max_fiber_even_majority_vote_successProb k =
        (Nat.fib (k + 2) : ℝ) / (Nat.fib (k + 4) : ℝ) := by
  rcases paper_pom_max_fiber_even_majority_vote k 1 with ⟨hcomp, -, hlog_pos, -, hneg⟩
  refine ⟨?_, ?_, rfl, hcomp⟩
  · rw [pom_max_fiber_even_majority_vote_logLikelihoodRatio]
    norm_num
    simpa using hlog_pos
  · exact (hneg 0).2 (by norm_num)

end Omega.POM
