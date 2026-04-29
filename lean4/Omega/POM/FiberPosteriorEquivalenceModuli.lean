import Mathlib.Tactic
import Omega.POM.FiberPosteriorEquivalenceFibonacciGauge

namespace Omega.POM

/-- The linearized activity map in log coordinates. -/
def pom_fiber_posterior_equivalence_moduli_log_activity_map (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  y (j + 1) + y (j + 2) - y j

/-- A recursive section of the linearized activity map, normalized by `y 0 = y 1 = 0`. -/
def pom_fiber_posterior_equivalence_moduli_log_activity_section (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      z n + pom_fiber_posterior_equivalence_moduli_log_activity_section z n -
        pom_fiber_posterior_equivalence_moduli_log_activity_section z (n + 1)

lemma pom_fiber_posterior_equivalence_moduli_log_activity_section_spec
    (z : ℕ → ℝ) (j : ℕ) :
    pom_fiber_posterior_equivalence_moduli_log_activity_map
        (pom_fiber_posterior_equivalence_moduli_log_activity_section z) j = z j := by
  simp [pom_fiber_posterior_equivalence_moduli_log_activity_map,
    pom_fiber_posterior_equivalence_moduli_log_activity_section]

lemma pom_fiber_posterior_equivalence_moduli_log_activity_surjective
    (m : ℕ) :
    ∀ z : ℕ → ℝ, ∃ y : ℕ → ℝ, ∀ j, j + 2 < m →
      pom_fiber_posterior_equivalence_moduli_log_activity_map y j = z j := by
  intro z
  refine ⟨pom_fiber_posterior_equivalence_moduli_log_activity_section z, ?_⟩
  intro j hj
  simpa using pom_fiber_posterior_equivalence_moduli_log_activity_section_spec z j

lemma pom_fiber_posterior_equivalence_moduli_linear_combo
    {m : ℕ} {u : ℕ → ℝ}
    (hrec : ∀ j, j + 2 < m → u j = u (j + 1) + u (j + 2)) :
    ∀ j, j < m →
      u j =
        u 0 * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
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

lemma pom_fiber_posterior_equivalence_moduli_kernel_iff
    (m : ℕ) (y : ℕ → ℝ) :
    (∀ j, j + 2 < m →
      pom_fiber_posterior_equivalence_moduli_log_activity_map y j = 0) ↔
      ∃ A B : ℝ, ∀ j, j < m →
        y j =
          A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j := by
  constructor
  · intro hkernel
    have hrec : ∀ j, j + 2 < m → y j = y (j + 1) + y (j + 2) := by
      intro j hj
      have hj0 := hkernel j hj
      dsimp [pom_fiber_posterior_equivalence_moduli_log_activity_map] at hj0
      linarith
    refine ⟨y 0, y 1, ?_⟩
    intro j hj
    simpa using pom_fiber_posterior_equivalence_moduli_linear_combo hrec j hj
  · rintro ⟨A, B, hAB⟩ j hj
    have hj0 : j < m := by omega
    have hj1 : j + 1 < m := by omega
    have hj2 : j + 2 < m := by omega
    rw [pom_fiber_posterior_equivalence_moduli_log_activity_map, hAB j hj0, hAB (j + 1) hj1,
      hAB (j + 2) hj2]
    have hα := pom_fiber_posterior_equivalence_fibonacci_gauge_alpha_recurrence j
    have hβ := pom_fiber_posterior_equivalence_fibonacci_gauge_beta_recurrence j
    have hα' :
        A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j =
          A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 1) +
            A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 2) := by
      calc
        A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j =
            A *
              (pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 1) +
                pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 2)) := by
              rw [hα]
        _ =
            A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 1) +
              A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha (j + 2) := by
              ring
    have hβ' :
        B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j =
          B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 1) +
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 2) := by
      calc
        B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j =
            B *
              (pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 1) +
                pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 2)) := by
              rw [hβ]
        _ =
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 1) +
              B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta (j + 2) := by
              ring
    nlinarith

lemma pom_fiber_posterior_equivalence_moduli_same_fiber_iff
    (m : ℕ) (y₁ y₂ : ℕ → ℝ) :
    (∀ j, j + 2 < m →
      pom_fiber_posterior_equivalence_moduli_log_activity_map y₁ j =
        pom_fiber_posterior_equivalence_moduli_log_activity_map y₂ j) ↔
      ∃ A B : ℝ, ∀ j, j < m →
        y₁ j - y₂ j =
          A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j := by
  constructor
  · intro hsame
    have hkernel :
        ∀ j, j + 2 < m →
          pom_fiber_posterior_equivalence_moduli_log_activity_map
              (fun k => y₁ k - y₂ k) j = 0 := by
      intro j hj
      have hj' := hsame j hj
      dsimp [pom_fiber_posterior_equivalence_moduli_log_activity_map] at hj' ⊢
      linarith
    exact (pom_fiber_posterior_equivalence_moduli_kernel_iff m (fun k => y₁ k - y₂ k)).1 hkernel
  · rintro ⟨A, B, hAB⟩ j hj
    have hkernel :=
      (pom_fiber_posterior_equivalence_moduli_kernel_iff m (fun k => y₁ k - y₂ k)).2
        ⟨A, B, hAB⟩
    have hj0 := hkernel j hj
    dsimp [pom_fiber_posterior_equivalence_moduli_log_activity_map] at hj0
    have hEq : y₁ (j + 1) + y₁ (j + 2) - y₁ j = y₂ (j + 1) + y₂ (j + 2) - y₂ j := by
      linarith
    simpa [pom_fiber_posterior_equivalence_moduli_log_activity_map] using hEq

lemma pom_fiber_posterior_equivalence_moduli_posterior_iff
    (m : ℕ) (p : ℕ → ℝ) (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j < 1) :
    sameActivityField m p ↔
      ∃ A B : ℝ, ∀ j, j < m →
        Real.log (posteriorActivityField p j) =
          A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
            B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j := by
  rw [sameActivityField_iff_logRatioRecurrence hp0 hp1]
  constructor
  · intro hrec
    have hkernel :
        ∀ j, j + 2 < m →
          pom_fiber_posterior_equivalence_moduli_log_activity_map
              (fun k => Real.log (posteriorActivityField p k)) j = 0 := by
      intro j hj
      have hj' := hrec j hj
      dsimp [pom_fiber_posterior_equivalence_moduli_log_activity_map] at hj' ⊢
      linarith
    exact
      (pom_fiber_posterior_equivalence_moduli_kernel_iff m
        (fun k => Real.log (posteriorActivityField p k))).1 hkernel
  · rintro ⟨A, B, hAB⟩ j hj
    have hkernel :=
      (pom_fiber_posterior_equivalence_moduli_kernel_iff m
        (fun k => Real.log (posteriorActivityField p k))).2 ⟨A, B, hAB⟩
    have hj0 := hkernel j hj
    dsimp [pom_fiber_posterior_equivalence_moduli_log_activity_map] at hj0
    linarith

/-- Paper-facing package: the linearized log-activity map is surjective, its fibers are affine
translates of the two-dimensional Fibonacci-gauge kernel, and posterior-equivalence classes are
exactly those fibers. -/
def pom_fiber_posterior_equivalence_moduli_statement (m : ℕ) : Prop :=
  (∀ z : ℕ → ℝ, ∃ y : ℕ → ℝ, ∀ j, j + 2 < m →
    pom_fiber_posterior_equivalence_moduli_log_activity_map y j = z j) ∧
    (∀ y₁ y₂ : ℕ → ℝ,
      (∀ j, j + 2 < m →
        pom_fiber_posterior_equivalence_moduli_log_activity_map y₁ j =
          pom_fiber_posterior_equivalence_moduli_log_activity_map y₂ j) ↔
        ∃ A B : ℝ, ∀ j, j < m →
          y₁ j - y₂ j =
            A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
              B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j) ∧
    (∀ p : ℕ → ℝ, ∀ (_ : ∀ j, 0 < p j), ∀ (_ : ∀ j, p j < 1),
      sameActivityField m p ↔
        ∃ A B : ℝ, ∀ j, j < m →
          Real.log (posteriorActivityField p j) =
            A * pom_fiber_posterior_equivalence_fibonacci_gauge_alpha j +
              B * pom_fiber_posterior_equivalence_fibonacci_gauge_beta j)

/-- Paper label: `prop:pom-fiber-posterior-equivalence-moduli`. -/
theorem paper_pom_fiber_posterior_equivalence_moduli
    (m : ℕ) : pom_fiber_posterior_equivalence_moduli_statement m := by
  refine ⟨pom_fiber_posterior_equivalence_moduli_log_activity_surjective m, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y₁ y₂
    exact pom_fiber_posterior_equivalence_moduli_same_fiber_iff m y₁ y₂
  · simpa using pom_fiber_posterior_equivalence_moduli_posterior_iff m

end Omega.POM
