import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Complementary Bernoulli parameter used for the majority-vote proxy. The Fibonacci index is
shifted so that all denominators stay strictly positive for every `k : ℕ`. -/
noncomputable def pom_max_fiber_even_majority_vote_successProb (k : Nat) : ℝ :=
  (Nat.fib (k + 3) : ℝ) / (Nat.fib (k + 4) : ℝ)

/-- Corresponding odds ratio. -/
noncomputable def pom_max_fiber_even_majority_vote_oddsRatio (k : Nat) : ℝ :=
  pom_max_fiber_even_majority_vote_successProb k /
    (1 - pom_max_fiber_even_majority_vote_successProb k)

/-- Scalar log-likelihood ratio as a function of the success count `S_n = s`. -/
noncomputable def pom_max_fiber_even_majority_vote_logLikelihoodRatio (k n s : Nat) : ℝ :=
  (((2 : ℤ) * s - n : ℤ) : ℝ) * Real.log (pom_max_fiber_even_majority_vote_oddsRatio k)

/-- Concrete majority-vote statement: the complementary parameter is Fibonacci, the odds ratio
reduces to a Fibonacci quotient, and the sign of the log-likelihood ratio is exactly the sign of
`2 * S_n - n`. -/
def pom_max_fiber_even_majority_vote_statement (k n : Nat) : Prop :=
  (1 - pom_max_fiber_even_majority_vote_successProb k =
      (Nat.fib (k + 2) : ℝ) / (Nat.fib (k + 4) : ℝ)) ∧
    (pom_max_fiber_even_majority_vote_oddsRatio k =
      (Nat.fib (k + 3) : ℝ) / (Nat.fib (k + 2) : ℝ)) ∧
    (0 < Real.log (pom_max_fiber_even_majority_vote_oddsRatio k)) ∧
    (∀ s : Nat, 0 ≤ pom_max_fiber_even_majority_vote_logLikelihoodRatio k n s ↔ n ≤ 2 * s) ∧
    (∀ s : Nat, pom_max_fiber_even_majority_vote_logLikelihoodRatio k n s < 0 ↔ 2 * s < n)

theorem paper_pom_max_fiber_even_majority_vote (k n : Nat) :
    pom_max_fiber_even_majority_vote_statement k n := by
  have hfib4_nat : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
    simpa [add_assoc, add_left_comm, add_comm] using (Nat.fib_add_two (n := k + 2))
  have hfib3_nat : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    simpa [add_assoc, add_left_comm, add_comm] using (Nat.fib_add_two (n := k + 1))
  have hfib4' : (Nat.fib (k + 4) : ℝ) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
    exact_mod_cast hfib4_nat
  have hfib3' : (Nat.fib (k + 3) : ℝ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    exact_mod_cast hfib3_nat
  have hfib4 : (Nat.fib (k + 4) : ℝ) = Nat.fib (k + 3) + Nat.fib (k + 2) := by
    simpa [add_comm] using hfib4'
  have hfib3 : (Nat.fib (k + 3) : ℝ) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
    simpa [add_comm] using hfib3'
  have hfib4_pos : 0 < (Nat.fib (k + 4) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < k + 4))
  have hfib2_pos : 0 < (Nat.fib (k + 2) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < k + 2))
  have hfib1_pos : 0 < (Nat.fib (k + 1) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < k + 1))
  have hfib4_ne : (Nat.fib (k + 4) : ℝ) ≠ 0 := ne_of_gt hfib4_pos
  have hfib2_ne : (Nat.fib (k + 2) : ℝ) ≠ 0 := ne_of_gt hfib2_pos
  have hcomp :
      1 - pom_max_fiber_even_majority_vote_successProb k =
        (Nat.fib (k + 2) : ℝ) / (Nat.fib (k + 4) : ℝ) := by
    unfold pom_max_fiber_even_majority_vote_successProb
    rw [hfib4]
    field_simp [hfib4_ne]
    ring
  have hodds :
      pom_max_fiber_even_majority_vote_oddsRatio k =
        (Nat.fib (k + 3) : ℝ) / (Nat.fib (k + 2) : ℝ) := by
    unfold pom_max_fiber_even_majority_vote_oddsRatio
    rw [hcomp]
    unfold pom_max_fiber_even_majority_vote_successProb
    field_simp [hfib2_ne, hfib4_ne]
  have hratio_gt_one : 1 < pom_max_fiber_even_majority_vote_oddsRatio k := by
    rw [hodds]
    have hlt : (Nat.fib (k + 2) : ℝ) < Nat.fib (k + 3) := by
      rw [hfib3]
      linarith
    have hdiv :
        (Nat.fib (k + 2) : ℝ) / (Nat.fib (k + 2) : ℝ) <
          (Nat.fib (k + 3) : ℝ) / (Nat.fib (k + 2) : ℝ) :=
      div_lt_div_of_pos_right hlt hfib2_pos
    simpa [hfib2_ne] using hdiv
  have hlog_pos : 0 < Real.log (pom_max_fiber_even_majority_vote_oddsRatio k) := by
    exact Real.log_pos hratio_gt_one
  refine ⟨hcomp, hodds, hlog_pos, ?_, ?_⟩
  · intro s
    rw [pom_max_fiber_even_majority_vote_logLikelihoodRatio]
    have hmul :
        0 ≤ (((2 : ℤ) * s - n : ℤ) : ℝ) * Real.log (pom_max_fiber_even_majority_vote_oddsRatio k) ↔
          0 ≤ (((2 : ℤ) * s - n : ℤ) : ℝ) := by
      exact mul_nonneg_iff_of_pos_right hlog_pos
    rw [hmul]
    constructor
    · intro hs
      have hs' : (n : ℝ) ≤ 2 * s := by
        norm_num at hs ⊢
        linarith
      exact_mod_cast hs'
    · intro hs
      have hs' : (n : ℝ) ≤ 2 * s := by
        exact_mod_cast hs
      norm_num
      linarith
  · intro s
    rw [pom_max_fiber_even_majority_vote_logLikelihoodRatio]
    have hmul :
        (((2 : ℤ) * s - n : ℤ) : ℝ) * Real.log (pom_max_fiber_even_majority_vote_oddsRatio k) < 0 ↔
          (((2 : ℤ) * s - n : ℤ) : ℝ) < 0 := by
      constructor
      · intro hs
        by_contra hnonneg
        have hnonneg' : 0 ≤ (((2 : ℤ) * s - n : ℤ) : ℝ) := le_of_not_gt hnonneg
        have hprod_nonneg :
            0 ≤ (((2 : ℤ) * s - n : ℤ) : ℝ) * Real.log (pom_max_fiber_even_majority_vote_oddsRatio k) :=
          mul_nonneg hnonneg' hlog_pos.le
        linarith
      · intro hs
        exact mul_neg_of_neg_of_pos hs hlog_pos
    rw [hmul]
    constructor
    · intro hs
      have hs' : (2 * s : ℝ) < n := by
        norm_num at hs ⊢
        linarith
      exact_mod_cast hs'
    · intro hs
      have hs' : (2 * s : ℝ) < n := by
        exact_mod_cast hs
      norm_num
      linarith

end Omega.POM
