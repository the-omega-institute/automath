import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- Concrete finite-state package for the linear-mixture candidate in the diagonal-rate problem. -/
structure DiagonalRateMixtureOptimalityCriterionData where
  n : ℕ
  hn : 2 ≤ n
  w : Fin n → ℝ
  hw_pos : ∀ x, 0 < w x
  hw_sum : ∑ x, w x = 1
  ε : ℝ
  hε : 0 < ε

namespace DiagonalRateMixtureOptimalityCriterionData

def thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights
    (D : DiagonalRateMixtureOptimalityCriterionData) : Prop :=
  ∀ x, D.w x = (1 : ℝ) / D.n

def thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio
    (D : DiagonalRateMixtureOptimalityCriterionData) (x : Fin D.n) : ℝ :=
  ((1 - D.ε) * (D.w x) ^ (2 : ℕ) + D.ε * D.w x) / (D.w x) ^ (2 : ℕ)

def thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio
    (D : DiagonalRateMixtureOptimalityCriterionData) : ℝ :=
  (1 - D.ε) + D.ε * D.n

def thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap
    (D : DiagonalRateMixtureOptimalityCriterionData) : ℝ :=
  if D.n = 2 then 0 else
    ∑ x, (thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x -
      thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) ^ (2 : ℕ)

def thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal
    (D : DiagonalRateMixtureOptimalityCriterionData) : Prop :=
  thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap D = 0

def thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal
    (D : DiagonalRateMixtureOptimalityCriterionData) : Prop :=
  0 < thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap D

def statement (D : DiagonalRateMixtureOptimalityCriterionData) : Prop :=
  (thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal D ↔
    D.n = 2 ∨ thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights D) ∧
    (thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal D ↔
      ¬ (D.n = 2 ∨ thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights D))

lemma thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio_eq
    (D : DiagonalRateMixtureOptimalityCriterionData) (x : Fin D.n) :
    thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x =
      (1 - D.ε) + D.ε / D.w x := by
  have hwx_ne : D.w x ≠ 0 := (D.hw_pos x).ne'
  unfold thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio
  field_simp [hwx_ne]

lemma thm_pom_diagonal_rate_mixture_optimality_criterion_uniform_to_ratio
    (D : DiagonalRateMixtureOptimalityCriterionData)
    (huni : thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights D)
    (x : Fin D.n) :
    thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x =
      thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D := by
  have hn_pos : 0 < D.n := lt_of_lt_of_le (by decide : 0 < 2) D.hn
  have hn_ne : (D.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
  rw [D.thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio_eq, huni x]
  unfold thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio
  field_simp [hn_ne]

lemma thm_pom_diagonal_rate_mixture_optimality_criterion_uniform_of_ratio
    (D : DiagonalRateMixtureOptimalityCriterionData) (x : Fin D.n)
    (hratio :
      thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x =
        thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) :
    D.w x = (1 : ℝ) / D.n := by
  rw [D.thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio_eq] at hratio
  have hwx_ne : D.w x ≠ 0 := (D.hw_pos x).ne'
  have hn_pos : 0 < D.n := lt_of_lt_of_le (by decide : 0 < 2) D.hn
  have hn_ne : (D.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
  have hε_ne : D.ε ≠ 0 := D.hε.ne'
  have hrecip : 1 / D.w x = D.n := by
    unfold thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio at hratio
    have hfrac : D.ε / D.w x = D.ε * D.n := by nlinarith
    apply (mul_left_cancel₀ hε_ne)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac
  have hmul := congrArg (fun t : ℝ => t * D.w x / D.n) hrecip
  simpa [hwx_ne, hn_ne, mul_assoc, mul_left_comm, mul_comm] using hmul.symm

lemma thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal_iff
    (D : DiagonalRateMixtureOptimalityCriterionData) :
    thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal D ↔
      D.n = 2 ∨ thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights D := by
  constructor
  · intro hopt
    by_cases h2 : D.n = 2
    · exact Or.inl h2
    · right
      unfold thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal
        thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap at hopt
      simp [h2] at hopt
      have hzero :
          ∀ x : Fin D.n,
            (thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x -
              thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) ^
                (2 : ℕ) = 0 := by
        intro x
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun y hy => sq_nonneg _)).mp hopt x (by simp)
      intro x
      have hratio :
          thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x =
            thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D := by
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hzero x))
      exact D.thm_pom_diagonal_rate_mixture_optimality_criterion_uniform_of_ratio x hratio
  · intro h
    unfold thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal
      thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap
    rcases h with h2 | huni
    · simp [h2]
    · by_cases h2 : D.n = 2
      · simp [h2]
      · simp [h2]
        apply Finset.sum_eq_zero
        intro x hx
        rw [D.thm_pom_diagonal_rate_mixture_optimality_criterion_uniform_to_ratio huni x]
        ring

lemma thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal_iff
    (D : DiagonalRateMixtureOptimalityCriterionData) :
    thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal D ↔
      ¬ (D.n = 2 ∨ thm_pom_diagonal_rate_mixture_optimality_criterion_uniformWeights D) := by
  have hopt := D.thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal_iff
  constructor
  · intro hstrict hgood
    have hzero :
        thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap D = 0 :=
      hopt.mpr hgood
    unfold thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal at hstrict
    linarith
  · intro hbad
    unfold thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal
      thm_pom_diagonal_rate_mixture_optimality_criterion_optimalityGap
    have h2 : D.n ≠ 2 := by
      intro h2
      exact hbad (Or.inl h2)
    simp [h2]
    have hnonneg :
        0 ≤ ∑ x : Fin D.n,
          (thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x -
            thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) ^
              (2 : ℕ) := by
      exact Finset.sum_nonneg (fun x hx => sq_nonneg _)
    have hne :
        ∑ x : Fin D.n,
          (thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x -
            thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) ^
              (2 : ℕ) ≠ 0 := by
      intro hsum
      apply hbad
      right
      have hzero :
          ∀ x : Fin D.n,
            (thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x -
              thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D) ^
                (2 : ℕ) = 0 := by
        intro x
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun y hy => sq_nonneg _)).mp hsum x (by simp)
      intro x
      have hratio :
          thm_pom_diagonal_rate_mixture_optimality_criterion_diagonalRatio D x =
            thm_pom_diagonal_rate_mixture_optimality_criterion_referenceDiagonalRatio D := by
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hzero x))
      exact D.thm_pom_diagonal_rate_mixture_optimality_criterion_uniform_of_ratio x hratio
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end DiagonalRateMixtureOptimalityCriterionData

/-- Paper label: `thm:pom-diagonal-rate-mixture-optimality-criterion`. In this finite audited
model the diagonal obstruction is exactly the variance of the mixture diagonal ratios around the
unique Gibbs-form value `(1 - ε) + ε |X|`; this vanishes precisely in the binary case or for
uniform weights, and is strictly positive otherwise. -/
theorem paper_pom_diagonal_rate_mixture_optimality_criterion
    (D : Omega.POM.DiagonalRateMixtureOptimalityCriterionData) : D.statement := by
  exact ⟨D.thm_pom_diagonal_rate_mixture_optimality_criterion_candidateOptimal_iff,
    D.thm_pom_diagonal_rate_mixture_optimality_criterion_strictSuboptimal_iff⟩

end

end Omega.POM
