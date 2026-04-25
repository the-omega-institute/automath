import Mathlib.Tactic
import Omega.POM.FiberPosteriorEquivalenceActivityField

namespace Omega.POM

/-- The first Fibonacci-gauge basis vector for the posterior log-ratio recurrence. -/
def pom_fiber_posterior_equivalence_fibonacci_gauge_alpha : Nat → Real
  | 0 => 1
  | 1 => 0
  | n + 2 => pom_fiber_posterior_equivalence_fibonacci_gauge_alpha n -
      pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 1)

/-- The second Fibonacci-gauge basis vector for the posterior log-ratio recurrence. -/
def pom_fiber_posterior_equivalence_fibonacci_gauge_beta : Nat → Real
  | 0 => 0
  | 1 => 1
  | n + 2 => pom_fiber_posterior_equivalence_fibonacci_gauge_beta n -
      pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 1)

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_zero :
    pom_fiber_posterior_equivalence_fibonacci_gauge_alpha 0 = 1 := rfl

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_one :
    pom_fiber_posterior_equivalence_fibonacci_gauge_alpha 1 = 0 := rfl

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_succ_succ (n : Nat) :
    pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 2) =
      pom_fiber_posterior_equivalence_fibonacci_gauge_alpha n -
        pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 1) := rfl

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_beta_zero :
    pom_fiber_posterior_equivalence_fibonacci_gauge_beta 0 = 0 := rfl

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_beta_one :
    pom_fiber_posterior_equivalence_fibonacci_gauge_beta 1 = 1 := rfl

@[simp] lemma pom_fiber_posterior_equivalence_fibonacci_gauge_beta_succ_succ (n : Nat) :
    pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 2) =
      pom_fiber_posterior_equivalence_fibonacci_gauge_beta n -
        pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 1) := rfl

lemma pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_recurrence (n : Nat) :
    pom_fiber_posterior_equivalence_fibonacci_gauge_alpha n =
      pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 1) +
        pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 2) := by
  rw [pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_succ_succ]
  ring

lemma pom_fiber_posterior_equivalence_fibonacci_gauge_beta_recurrence (n : Nat) :
    pom_fiber_posterior_equivalence_fibonacci_gauge_beta n =
      pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 1) +
        pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 2) := by
  rw [pom_fiber_posterior_equivalence_fibonacci_gauge_beta_succ_succ]
  ring

private lemma paper_pom_fiber_posterior_equivalence_fibonacci_gauge_linear_combo
    {m : Nat} {u : Nat → Real}
    (hrec : ∀ j, j + 2 < m → u j = u (j + 1) + u (j + 2)) :
    ∀ j, j < m →
      u j = u 0 * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
        u 1 * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j := by
  refine Nat.twoStepInduction ?_ ?_ ?_
  · intro hj
    simp
  · intro hj
    simp
  · intro n ihn ihn1 hj
    have hrecn : u n = u (n + 1) + u (n + 2) := hrec n hj
    have hn : n < m := by omega
    have hn1 : n + 1 < m := by omega
    calc
      u (n + 2) = u n - u (n + 1) := by linarith
      _ =
          (u 0 * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha n +
              u 1 * pom_fiber_posterior_equivalence_fibonacci_gauge_beta n) -
            (u 0 * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 1) +
              u 1 * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 1)) := by
            rw [ihn hn, ihn1 hn1]
      _ =
          u 0 * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (n + 2) +
            u 1 * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (n + 2) := by
            rw [pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_succ_succ,
              pom_fiber_posterior_equivalence_fibonacci_gauge_beta_succ_succ]
            ring

/-- Paper label: `cor:pom-fiber-posterior-equivalence-fibonacci-gauge`. -/
theorem paper_pom_fiber_posterior_equivalence_fibonacci_gauge
    (m : Nat) (hm : 3 ≤ m) (p : Nat → Real) (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j < 1) :
    sameActivityField m p ↔
      ∃ A B : Real, ∀ j, j < m →
        Real.log (posteriorActivityField p j) =
          A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j := by
  let u : Nat → Real := fun j => Real.log (posteriorActivityField p j)
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  rw [sameActivityField_iff_logRatioRecurrence hp0 hp1]
  constructor
  · intro hrec
    refine ⟨u 0, u 1, ?_⟩
    intro j hj
    simpa [u] using
      paper_pom_fiber_posterior_equivalence_fibonacci_gauge_linear_combo hrec j hj
  · rintro ⟨A, B, hAB⟩
    intro j hj
    have hj0 : j < m := by omega
    have hj1 : j + 1 < m := by omega
    have hj2 : j + 2 < m := by omega
    rw [hAB j hj0, hAB (j + 1) hj1, hAB (j + 2) hj2]
    rw [pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_recurrence,
      pom_fiber_posterior_equivalence_fibonacci_gauge_beta_recurrence]
    ring

end Omega.POM
