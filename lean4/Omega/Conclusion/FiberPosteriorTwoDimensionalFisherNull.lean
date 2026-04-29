import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.VisibleFiniteTypeFibonacciCompleteAudit
import Omega.POM.MicrocanonicalPosteriorModuliCLT

namespace Omega.Conclusion

/-- Four-dimensional readout keeping only the first two coordinates. -/
def conclusion_fiber_posterior_two_dimensional_fisher_null_L :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun y := fun i =>
    match i.1 with
    | 0 => y 0
    | _ => y 1
  map_add' := by
    intro y z
    ext i
    fin_cases i <;> rfl
  map_smul' := by
    intro a y
    ext i
    fin_cases i <;> rfl

/-- Logistic posterior coordinate attached to a scalar score. -/
noncomputable def conclusion_fiber_posterior_two_dimensional_fisher_null_logistic (t : ℝ) : ℝ :=
  1 / (1 + Real.exp (-t))

/-- Single-candidate posterior, written through the two-coordinate readout `L y`. -/
noncomputable def conclusion_fiber_posterior_two_dimensional_fisher_null_posterior
    (y : Fin 4 → ℝ) (i : Fin 2) : ℝ :=
  conclusion_fiber_posterior_two_dimensional_fisher_null_logistic
    (conclusion_fiber_posterior_two_dimensional_fisher_null_L y i)

/-- Diagonal logistic Fisher weights on the readout coordinates. -/
noncomputable def conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
    (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  conclusion_fiber_posterior_two_dimensional_fisher_null_logistic (z i) *
    (1 - conclusion_fiber_posterior_two_dimensional_fisher_null_logistic (z i))

/-- Pullback of the diagonal Fisher form along `L`. -/
noncomputable def conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher
    (y u : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 2,
    conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
        (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) i *
      (conclusion_fiber_posterior_two_dimensional_fisher_null_L u i) ^ 2

@[simp] lemma conclusion_fiber_posterior_two_dimensional_fisher_null_L_zero (y : Fin 4 → ℝ) :
    conclusion_fiber_posterior_two_dimensional_fisher_null_L y 0 = y 0 := rfl

@[simp] lemma conclusion_fiber_posterior_two_dimensional_fisher_null_L_one (y : Fin 4 → ℝ) :
    conclusion_fiber_posterior_two_dimensional_fisher_null_L y 1 = y 1 := rfl

private lemma conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_pos (t : ℝ) :
    0 < conclusion_fiber_posterior_two_dimensional_fisher_null_logistic t := by
  unfold conclusion_fiber_posterior_two_dimensional_fisher_null_logistic
  positivity

private lemma conclusion_fiber_posterior_two_dimensional_fisher_null_one_sub_logistic (t : ℝ) :
    1 - conclusion_fiber_posterior_two_dimensional_fisher_null_logistic t =
      Real.exp (-t) / (1 + Real.exp (-t)) := by
  unfold conclusion_fiber_posterior_two_dimensional_fisher_null_logistic
  field_simp
  ring

private lemma conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_lt_one (t : ℝ) :
    conclusion_fiber_posterior_two_dimensional_fisher_null_logistic t < 1 := by
  have hsub :
      0 < 1 - conclusion_fiber_posterior_two_dimensional_fisher_null_logistic t := by
    rw [conclusion_fiber_posterior_two_dimensional_fisher_null_one_sub_logistic]
    positivity
  linarith

/-- Concrete chapter-local statement packaging the posterior/readout dependence, the pulled-back
Fisher form, the explicit two-dimensional nullspace, and the already formalized posterior-moduli
and Fibonacci-gauge wrappers reused in the conclusion. -/
def ConclusionFiberPosteriorTwoDimensionalFisherNullStatement : Prop :=
  (∀ y : Fin 4 → ℝ, ∀ i : Fin 2,
    conclusion_fiber_posterior_two_dimensional_fisher_null_posterior y i =
      conclusion_fiber_posterior_two_dimensional_fisher_null_logistic
        (conclusion_fiber_posterior_two_dimensional_fisher_null_L y i)) ∧
    (∀ y u : Fin 4 → ℝ,
      conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher y u =
        conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
            (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 0 * (u 0) ^ 2 +
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
              (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 1 * (u 1) ^ 2) ∧
    (∀ y u : Fin 4 → ℝ,
      conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher y u = 0 ↔
        u 0 = 0 ∧ u 1 = 0) ∧
    Omega.POM.pomMicrocanonicalPosteriorModuliCLTStatement (1 / 2 : ℝ) 0 0 ∧
    (((0 : ℕ) < 1 ↔ ∃ N, N = 1) ∧ ((∃ N, N = 1) ↔ ∃ k, Nat.fib k = 1))

/-- Paper label: `thm:conclusion-fiber-posterior-two-dimensional-fisher-null`. -/
theorem paper_conclusion_fiber_posterior_two_dimensional_fisher_null :
    ConclusionFiberPosteriorTwoDimensionalFisherNullStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y i
    rfl
  · intro y u
    unfold conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher
    simp
  · intro y u
    have hg0 :
        0 <
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
            (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 0 := by
      unfold conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
      have hpos :=
        conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_pos
          (conclusion_fiber_posterior_two_dimensional_fisher_null_L y 0)
      have hlt :=
        conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_lt_one
          (conclusion_fiber_posterior_two_dimensional_fisher_null_L y 0)
      nlinarith
    have hg1 :
        0 <
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
            (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 1 := by
      unfold conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
      have hpos :=
        conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_pos
          (conclusion_fiber_posterior_two_dimensional_fisher_null_L y 1)
      have hlt :=
        conclusion_fiber_posterior_two_dimensional_fisher_null_logistic_lt_one
          (conclusion_fiber_posterior_two_dimensional_fisher_null_L y 1)
      nlinarith
    constructor
    · intro hzero
      have hrewrite :
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
              (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 0 * (u 0) ^ 2 +
            conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
                (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 1 * (u 1) ^ 2 = 0 := by
        simpa [conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher] using hzero
      have h0nonneg :
          0 ≤
            conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
                (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 0 * (u 0) ^ 2 := by
        positivity
      have h1nonneg :
          0 ≤
            conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
                (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 1 * (u 1) ^ 2 := by
        positivity
      have h0zero :
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
              (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 0 * (u 0) ^ 2 = 0 := by
        nlinarith
      have h1zero :
          conclusion_fiber_posterior_two_dimensional_fisher_null_fisher_diagonal
              (conclusion_fiber_posterior_two_dimensional_fisher_null_L y) 1 * (u 1) ^ 2 = 0 := by
        nlinarith
      have hu0sq : (u 0) ^ 2 = 0 := by
        exact (mul_eq_zero.mp h0zero).resolve_left (ne_of_gt hg0)
      have hu1sq : (u 1) ^ 2 = 0 := by
        exact (mul_eq_zero.mp h1zero).resolve_left (ne_of_gt hg1)
      constructor <;> nlinarith
    · rintro ⟨hu0, hu1⟩
      simp [conclusion_fiber_posterior_two_dimensional_fisher_null_pullback_fisher, hu0, hu1]
  · simpa using Omega.POM.paper_pom_microcanonical_posterior_moduli_clt (1 / 2 : ℝ) 0 0
  · have hDefect : ((0 : ℕ) < 1) ↔ ∃ N, N = 1 := by
      constructor
      · intro _
        exact ⟨1, rfl⟩
      · rintro ⟨N, hN⟩
        omega
    have hFib : ∀ {N : ℕ}, N = 1 → ∃ k, N ≤ Nat.fib k ∧ Nat.fib k = 1 := by
      intro N hN
      refine ⟨1, ?_, by simp⟩
      simp [hN]
    simpa using
      paper_conclusion_visible_finite_type_fibonacci_complete_audit 1 (fun N => N = 1) hDefect
        (fun {_} hN => hFib hN)

end Omega.Conclusion
