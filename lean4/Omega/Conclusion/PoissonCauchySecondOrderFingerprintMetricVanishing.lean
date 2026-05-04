import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete second-order fingerprint coordinates `(A, B)` from the Poisson--Cauchy expansion. -/
structure conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data where
  A : ℝ
  B : ℝ

/-- The traceless quadrupole representative vanishes. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_qZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  D.A / 2 = 0 ∧ D.B = 0 ∧ -D.A / 2 = 0

/-- The two fingerprint coordinates vanish. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  D.A = 0 ∧ D.B = 0

/-- The KL sharp second-order metric coefficient. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klCoeff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : ℝ :=
  D.A ^ 2 / 8 + D.B ^ 2 / 2

/-- The Fisher sharp second-order metric coefficient. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherCoeff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : ℝ :=
  D.A ^ 2 / 2 + 2 * D.B ^ 2

/-- The optimally projected KL second-order metric coefficient. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedCoeff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : ℝ :=
  D.A ^ 2 / 16 + D.B ^ 2 / 4

/-- The numerator polynomial inside the TV sharp-limit integrand. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvPolynomial
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data)
    (y : ℝ) : ℝ :=
  D.A * (3 * y ^ 2 - 1) - 2 * D.B * y * (3 - y ^ 2)

/-- The KL metric vanishing condition. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klCoeff D = 0

/-- The Fisher metric vanishing condition. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherCoeff D = 0

/-- The projected KL metric vanishing condition. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedCoeff D = 0

/-- The TV sharp-limit condition, reduced to zero numerator polynomial. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  ∀ y : ℝ,
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvPolynomial D y = 0

/-- The optimal drift coordinates vanish. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_driftZero
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  D.B = 0 ∧ D.A = 0

lemma conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_kl_zero_iff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) :
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D := by
  constructor
  · intro h
    dsimp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klCoeff] at h
    have hA : 0 ≤ D.A ^ 2 := sq_nonneg D.A
    have hB : 0 ≤ D.B ^ 2 := sq_nonneg D.B
    constructor <;> nlinarith
  · rintro ⟨hA, hB⟩
    simp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klCoeff, hA, hB]

lemma conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisher_zero_iff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) :
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D := by
  constructor
  · intro h
    dsimp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherCoeff] at h
    have hA : 0 ≤ D.A ^ 2 := sq_nonneg D.A
    have hB : 0 ≤ D.B ^ 2 := sq_nonneg D.B
    constructor <;> nlinarith
  · rintro ⟨hA, hB⟩
    simp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherCoeff, hA, hB]

lemma conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projected_zero_iff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) :
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D := by
  constructor
  · intro h
    dsimp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedCoeff] at h
    have hA : 0 ≤ D.A ^ 2 := sq_nonneg D.A
    have hB : 0 ≤ D.B ^ 2 := sq_nonneg D.B
    constructor <;> nlinarith
  · rintro ⟨hA, hB⟩
    simp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedZero,
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedCoeff, hA, hB]

lemma conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tv_zero_iff
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) :
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    dsimp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvPolynomial]
      at h0 h1
    constructor <;> nlinarith
  · rintro ⟨hA, hB⟩ y
    simp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvPolynomial,
      hA, hB]

/-- Paper-facing sixfold metric-vanishing equivalence plus optimal drift vanishing. -/
def conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_statement
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) : Prop :=
  (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_qZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D) ∧
    (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_klZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D) ∧
    (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisherZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D) ∧
    (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projectedZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D) ∧
    (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tvZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D) ∧
    (conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_driftZero D ↔
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_coordsZero D)

/-- Paper label: `thm:conclusion-poisson-cauchy-second-order-fingerprint-metric-vanishing`. -/
theorem paper_conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing
    (D : conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_data) :
    conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hA, hB, _hA'⟩
      exact ⟨by nlinarith, hB⟩
    · rintro ⟨hA, hB⟩
      simp [conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_qZero,
        hA, hB]
  · exact conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_kl_zero_iff D
  · exact conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_fisher_zero_iff D
  · exact
      conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_projected_zero_iff D
  · exact conclusion_poisson_cauchy_second_order_fingerprint_metric_vanishing_tv_zero_iff D
  · constructor
    · rintro ⟨hB, hA⟩
      exact ⟨hA, hB⟩
    · rintro ⟨hA, hB⟩
      exact ⟨hB, hA⟩

end

end Omega.Conclusion
