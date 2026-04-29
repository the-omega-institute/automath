import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.DeltaqHalfThresholdCriterion

namespace Omega.Conclusion

open Omega.POM

/-- Conclusion-level normalization of the bulk spectral dimension by `log φ`. -/
noncomputable def conclusion_kernel_rh_codimension_identity_bulk_dimension
    (rq : ℕ → ℝ) (q : ℕ) : ℝ :=
  Real.log (rq q) / Real.log Real.goldenRatio

/-- Conclusion-level normalization of the boundary spectral dimension by `log φ`. -/
noncomputable def conclusion_kernel_rh_codimension_identity_boundary_dimension
    (Lambdaq : ℕ → ℝ) (q : ℕ) : ℝ :=
  Real.log (Lambdaq q) / Real.log Real.goldenRatio

/-- Conclusion-level normalized correlation codimension. -/
noncomputable def conclusion_kernel_rh_codimension_identity_correlation_codimension
    (rq Lambdaq : ℕ → ℝ) (q : ℕ) : ℝ :=
  -pomDeltaq rq Lambdaq q / Real.log Real.goldenRatio

/-- The conclusion-level `β^{RH}` normalization: the boundary dimension is written as
`betaRh(q)` times the bulk dimension. -/
def conclusion_kernel_rh_codimension_identity_beta_relation
    (rq Lambdaq betaRh : ℕ → ℝ) (q : ℕ) : Prop :=
  betaRh q * conclusion_kernel_rh_codimension_identity_bulk_dimension rq q =
    conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q

/-- Paper-facing codimension identity and half-threshold equivalence in the conclusion notation. -/
def conclusion_kernel_rh_codimension_identity_statement
    (rq Lambdaq betaRh : ℕ → ℝ) (q : ℕ) : Prop :=
  pomDeltaq rq Lambdaq q / Real.log Real.goldenRatio =
      2 * conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q -
        conclusion_kernel_rh_codimension_identity_bulk_dimension rq q ∧
    conclusion_kernel_rh_codimension_identity_correlation_codimension rq Lambdaq q =
      -pomDeltaq rq Lambdaq q / Real.log Real.goldenRatio ∧
    (pomDeltaq rq Lambdaq q = 0 ↔
      conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q =
        conclusion_kernel_rh_codimension_identity_bulk_dimension rq q / 2) ∧
    (conclusion_kernel_rh_codimension_identity_beta_relation rq Lambdaq betaRh q →
      conclusion_kernel_rh_codimension_identity_bulk_dimension rq q ≠ 0 →
        (pomDeltaq rq Lambdaq q = 0 ↔ betaRh q = 1 / 2))

/-- Paper label: `thm:conclusion-kernel-rh-codimension-identity`. The conclusion-level bulk and
boundary dimensions are just the earlier logarithmic quantities normalized by `log φ`, so the
existing `δ_q` identity and half-threshold criterion rewrite directly into the codimension formula
and the `β^{RH}`-notation equivalence. -/
theorem paper_conclusion_kernel_rh_codimension_identity
    (rq Lambdaq betaRh : ℕ → ℝ) (q : ℕ) (hLambda : 0 < Lambdaq q) (hrq : 0 < rq q) :
    conclusion_kernel_rh_codimension_identity_statement rq Lambdaq betaRh q := by
  have hlogphi_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hlogphi_ne : Real.log Real.goldenRatio ≠ 0 := ne_of_gt hlogphi_pos
  have hδ :
      pomDeltaq rq Lambdaq q =
        2 * Real.log (Lambdaq q) - Real.log (rq q) := by
    calc
      pomDeltaq rq Lambdaq q = Real.log ((Lambdaq q) ^ 2) - Real.log (rq q) := by
        unfold pomDeltaq
        rw [Real.log_div (pow_ne_zero 2 hLambda.ne') hrq.ne']
      _ = 2 * Real.log (Lambdaq q) - Real.log (rq q) := by
        rw [Real.log_pow]
        ring
  have hHalf :
      pomDeltaq rq Lambdaq q = 0 ↔
        2 * pomBulkSpectralDimension Lambdaq q = pomBoundarySpectralDimension rq q :=
    paper_pom_deltaq_half_threshold_criterion rq Lambdaq q hLambda hrq
  have hHalf' :
      pomDeltaq rq Lambdaq q = 0 ↔
        conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q =
          conclusion_kernel_rh_codimension_identity_bulk_dimension rq q / 2 := by
    constructor
    · intro hZero
      have hEq :
          2 * pomBulkSpectralDimension Lambdaq q = pomBoundarySpectralDimension rq q :=
        hHalf.mp hZero
      simp [conclusion_kernel_rh_codimension_identity_boundary_dimension,
        conclusion_kernel_rh_codimension_identity_bulk_dimension,
        pomBulkSpectralDimension, pomBoundarySpectralDimension] at hEq ⊢
      field_simp [hlogphi_ne]
      linarith
    · intro hDim
      have hEq :
          2 * pomBulkSpectralDimension Lambdaq q = pomBoundarySpectralDimension rq q := by
        simp [conclusion_kernel_rh_codimension_identity_boundary_dimension,
          conclusion_kernel_rh_codimension_identity_bulk_dimension] at hDim
        field_simp [hlogphi_ne] at hDim
        simp [pomBulkSpectralDimension, pomBoundarySpectralDimension]
        nlinarith
      exact hHalf.mpr hEq
  refine ⟨?_, by rfl, hHalf', ?_⟩
  · unfold conclusion_kernel_rh_codimension_identity_boundary_dimension
      conclusion_kernel_rh_codimension_identity_bulk_dimension
    rw [hδ]
    field_simp [hlogphi_ne]
  · intro hBeta hBulk_nonzero
    rw [hHalf']
    let paper_label_conclusion_kernel_rh_codimension_identity_bulk :=
      conclusion_kernel_rh_codimension_identity_bulk_dimension rq q
    have hBeta' : betaRh q * paper_label_conclusion_kernel_rh_codimension_identity_bulk =
        conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q := by
      simpa [paper_label_conclusion_kernel_rh_codimension_identity_bulk,
        conclusion_kernel_rh_codimension_identity_beta_relation] using hBeta
    constructor
    · intro hDim
      have hEq : betaRh q * paper_label_conclusion_kernel_rh_codimension_identity_bulk =
          paper_label_conclusion_kernel_rh_codimension_identity_bulk / 2 := by
        rwa [hDim] at hBeta'
      have hDiv := congrArg
        (fun x : ℝ => x / paper_label_conclusion_kernel_rh_codimension_identity_bulk) hEq
      field_simp [paper_label_conclusion_kernel_rh_codimension_identity_bulk, hBulk_nonzero] at hDiv
      linarith
    · intro hBetaHalf
      calc
        conclusion_kernel_rh_codimension_identity_boundary_dimension Lambdaq q =
            betaRh q * paper_label_conclusion_kernel_rh_codimension_identity_bulk := by
              simpa using hBeta'.symm
        _ = paper_label_conclusion_kernel_rh_codimension_identity_bulk / 2 := by
              rw [hBetaHalf]
              ring

end Omega.Conclusion
