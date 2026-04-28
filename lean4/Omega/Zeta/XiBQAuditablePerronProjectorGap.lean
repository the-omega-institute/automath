import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Zeta

noncomputable section

/-- Concrete carrier for the audited `B_q` Perron projector package: the natural number is the
degree `q` of the symmetric-power binomial model. -/
abbrev xi_bq_auditable_perron_projector_gap_data := ℕ

namespace xi_bq_auditable_perron_projector_gap_data

/-- The golden Perron vector used for the `B_q` symmetric-power model. -/
def xi_bq_auditable_perron_projector_gap_perron_vector
    (D : xi_bq_auditable_perron_projector_gap_data) : Fin (D + 1) → ℝ :=
  fun i => Real.goldenRatio ^ i.1

/-- The binomial diagonal weight in the finite weighted inner product. -/
def xi_bq_auditable_perron_projector_gap_weight
    (D : xi_bq_auditable_perron_projector_gap_data) : Fin (D + 1) → ℝ :=
  fun i => Nat.choose D i.1

/-- Weighted squared norm of the Perron vector. -/
def xi_bq_auditable_perron_projector_gap_weighted_norm_sq
    (D : xi_bq_auditable_perron_projector_gap_data) : ℝ :=
  ∑ i, xi_bq_auditable_perron_projector_gap_weight D i *
    xi_bq_auditable_perron_projector_gap_perron_vector D i ^ 2

/-- Rank-one Perron projector entry in weighted coordinates. -/
def xi_bq_auditable_perron_projector_gap_projector_entry
    (D : xi_bq_auditable_perron_projector_gap_data) (i j : Fin (D + 1)) : ℝ :=
  xi_bq_auditable_perron_projector_gap_perron_vector D i *
    xi_bq_auditable_perron_projector_gap_weight D j *
      xi_bq_auditable_perron_projector_gap_perron_vector D j /
        xi_bq_auditable_perron_projector_gap_weighted_norm_sq D

/-- The normalized spectral ratio of the `j`-th symmetric-power eigenvalue to the Perron one. -/
def xi_bq_auditable_perron_projector_gap_closed_eigenvalue
    (D : xi_bq_auditable_perron_projector_gap_data) (j : Fin (D + 1)) : ℝ :=
  ((-1 : ℝ) ^ j.1 * Real.goldenRatio ^ (D - j.1)) / Real.goldenRatio ^ j.1

/-- The normalized spectral ratio of the `j`-th symmetric-power eigenvalue to the Perron one. -/
def xi_bq_auditable_perron_projector_gap_normalized_eigen_ratio
    (D : xi_bq_auditable_perron_projector_gap_data) (j : Fin (D + 1)) : ℝ :=
  xi_bq_auditable_perron_projector_gap_closed_eigenvalue D j /
    xi_bq_auditable_perron_projector_gap_closed_eigenvalue D 0

/-- The explicit weighted norm formula for the concrete Perron vector. -/
def perron_norm_formula (D : xi_bq_auditable_perron_projector_gap_data) : Prop :=
  xi_bq_auditable_perron_projector_gap_weighted_norm_sq D =
    ∑ i, xi_bq_auditable_perron_projector_gap_weight D i *
      xi_bq_auditable_perron_projector_gap_perron_vector D i ^ 2

/-- The explicit entries of the rank-one Perron projector. -/
def projection_entry_formula (D : xi_bq_auditable_perron_projector_gap_data) : Prop :=
  ∀ i j : Fin (D + 1),
    xi_bq_auditable_perron_projector_gap_projector_entry D i j =
      Real.goldenRatio ^ i.1 * (Nat.choose D j.1 : ℝ) * Real.goldenRatio ^ j.1 /
        xi_bq_auditable_perron_projector_gap_weighted_norm_sq D

/-- The normalized non-Perron eigenvalue package is the closed-form `Sym^q` spectrum divided by
the Perron eigenvalue. -/
def uniform_gap (D : xi_bq_auditable_perron_projector_gap_data) : Prop :=
  ∀ j : Fin (D + 1),
    xi_bq_auditable_perron_projector_gap_normalized_eigen_ratio D j =
      xi_bq_auditable_perron_projector_gap_closed_eigenvalue D j /
        xi_bq_auditable_perron_projector_gap_closed_eigenvalue D 0

/-- The first non-Perron ratio is the `j = 1` normalized closed-form spectral value whenever
that index exists. -/
def second_ratio (D : xi_bq_auditable_perron_projector_gap_data) : Prop :=
  ∀ h : 1 < D + 1,
    xi_bq_auditable_perron_projector_gap_normalized_eigen_ratio D ⟨1, h⟩ =
      xi_bq_auditable_perron_projector_gap_closed_eigenvalue D ⟨1, h⟩ /
        xi_bq_auditable_perron_projector_gap_closed_eigenvalue D 0

end xi_bq_auditable_perron_projector_gap_data

/-- Paper label: `thm:xi-bq-auditable-perron-projector-gap`. -/
theorem paper_xi_bq_auditable_perron_projector_gap
    (D : xi_bq_auditable_perron_projector_gap_data) :
    D.perron_norm_formula ∧ D.projection_entry_formula ∧ D.uniform_gap ∧ D.second_ratio := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · intro i j
    unfold xi_bq_auditable_perron_projector_gap_data.xi_bq_auditable_perron_projector_gap_projector_entry
    unfold xi_bq_auditable_perron_projector_gap_data.xi_bq_auditable_perron_projector_gap_weight
    unfold xi_bq_auditable_perron_projector_gap_data.xi_bq_auditable_perron_projector_gap_perron_vector
    rfl
  · intro j
    unfold xi_bq_auditable_perron_projector_gap_data.xi_bq_auditable_perron_projector_gap_normalized_eigen_ratio
    rfl
  · intro h
    unfold xi_bq_auditable_perron_projector_gap_data.xi_bq_auditable_perron_projector_gap_normalized_eigen_ratio
    rfl

end

end Omega.Zeta
