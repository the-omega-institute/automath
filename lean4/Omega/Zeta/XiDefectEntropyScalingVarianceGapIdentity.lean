import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite weighted family for
`prop:xi-defect-entropy-scaling-variance-gap-identity`. -/
structure xi_defect_entropy_scaling_variance_gap_identity_data where
  n : ℕ
  weights : Fin n → ℝ
  probabilities : Fin n → ℝ
  kappa : ℝ
  derivative : ℝ
  kappa_eq_weight_sum : kappa = ∑ j, weights j
  kappa_pos : 0 < kappa
  weights_nonneg : ∀ j, 0 ≤ weights j
  derivative_eq_logistic_sum :
    derivative = ∑ j, weights j * probabilities j * (1 - probabilities j)

/-- Weighted total mass `S(s)` at a fixed flow time. -/
noncomputable def xi_defect_entropy_scaling_variance_gap_identity_total
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) : ℝ :=
  ∑ j, D.weights j * D.probabilities j

/-- Weighted mean `S(s) / κ`. -/
noncomputable def xi_defect_entropy_scaling_variance_gap_identity_mean
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) : ℝ :=
  xi_defect_entropy_scaling_variance_gap_identity_total D / D.kappa

/-- The unnormalized weighted variance gap `κ Var_m(p(s))`. -/
noncomputable def xi_defect_entropy_scaling_variance_gap_identity_variance_gap
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) : ℝ :=
  ∑ j, D.weights j *
    (D.probabilities j - xi_defect_entropy_scaling_variance_gap_identity_mean D) ^ 2

/-- Concrete statement: exact variance-gap identity and the logistic upper bound. -/
noncomputable def xi_defect_entropy_scaling_variance_gap_identity_statement
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) : Prop :=
  D.derivative =
      xi_defect_entropy_scaling_variance_gap_identity_total D *
          (1 - xi_defect_entropy_scaling_variance_gap_identity_total D / D.kappa) -
        xi_defect_entropy_scaling_variance_gap_identity_variance_gap D ∧
    D.derivative ≤
      xi_defect_entropy_scaling_variance_gap_identity_total D *
        (1 - xi_defect_entropy_scaling_variance_gap_identity_total D / D.kappa)

lemma xi_defect_entropy_scaling_variance_gap_identity_gap_nonneg
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) :
    0 ≤ xi_defect_entropy_scaling_variance_gap_identity_variance_gap D := by
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (D.weights_nonneg j) (sq_nonneg _)

lemma xi_defect_entropy_scaling_variance_gap_identity_sum_identity
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) :
    (∑ j, D.weights j * D.probabilities j * (1 - D.probabilities j)) =
      xi_defect_entropy_scaling_variance_gap_identity_total D *
          (1 - xi_defect_entropy_scaling_variance_gap_identity_total D / D.kappa) -
        xi_defect_entropy_scaling_variance_gap_identity_variance_gap D := by
  classical
  set S := xi_defect_entropy_scaling_variance_gap_identity_total D with hS
  have hkappa_ne : D.kappa ≠ 0 := ne_of_gt D.kappa_pos
  have hsum_weights : (∑ j, D.weights j) = D.kappa := by
    simpa using D.kappa_eq_weight_sum.symm
  have hsum_weighted : (∑ j, D.weights j * D.probabilities j) = S := by
    exact hS.symm
  have hvariance :
      xi_defect_entropy_scaling_variance_gap_identity_variance_gap D =
        (∑ j, D.weights j * D.probabilities j ^ 2) - S ^ 2 / D.kappa := by
    simp only [xi_defect_entropy_scaling_variance_gap_identity_variance_gap,
      xi_defect_entropy_scaling_variance_gap_identity_mean]
    rw [← hS]
    trans (∑ j, (D.weights j * D.probabilities j ^ 2 -
        (2 * (S / D.kappa)) * (D.weights j * D.probabilities j) +
          (S / D.kappa) ^ 2 * D.weights j))
    · refine Finset.sum_congr rfl ?_
      intro j hj
      ring
    · rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hsum_weighted, hsum_weights]
      field_simp [hkappa_ne]
      ring
  have hlogistic_sum :
      (∑ j, D.weights j * D.probabilities j * (1 - D.probabilities j)) =
        S - ∑ j, D.weights j * D.probabilities j ^ 2 := by
    trans ∑ j, (D.weights j * D.probabilities j -
        D.weights j * D.probabilities j ^ 2)
    · refine Finset.sum_congr rfl ?_
      intro j hj
      ring
    · rw [Finset.sum_sub_distrib, hsum_weighted]
  rw [hlogistic_sum, hvariance]
  field_simp [hkappa_ne]
  ring

/-- Paper label: `prop:xi-defect-entropy-scaling-variance-gap-identity`. -/
theorem paper_xi_defect_entropy_scaling_variance_gap_identity
    (D : xi_defect_entropy_scaling_variance_gap_identity_data) :
    xi_defect_entropy_scaling_variance_gap_identity_statement D := by
  constructor
  · rw [D.derivative_eq_logistic_sum]
    exact xi_defect_entropy_scaling_variance_gap_identity_sum_identity D
  · rw [D.derivative_eq_logistic_sum]
    rw [xi_defect_entropy_scaling_variance_gap_identity_sum_identity D]
    linarith [xi_defect_entropy_scaling_variance_gap_identity_gap_nonneg D]

end Omega.Zeta
