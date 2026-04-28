import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete coefficient data for the one-target Laguerre denominator reconstruction.

The record stores the denominator coefficients `d_j`, the punctured characteristic
coefficients `p_j`, the leading coefficient inverse, and the final normalization data. -/
structure conclusion_critical_kernel_one_target_denominator_reconstruction_data where
  conclusion_critical_kernel_one_target_denominator_reconstruction_degree : ℕ
  conclusion_critical_kernel_one_target_denominator_reconstruction_kappa : ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff : ℕ → ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_denominatorCoeff : ℕ → ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv : ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_targetParameter : ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_remainingReciprocalSum : ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_parameter : ℕ → ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_distribution : ℕ → ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_distributionNormalizer : ℝ
  conclusion_critical_kernel_one_target_denominator_reconstruction_coeffCompare :
    ∀ j : ℕ,
      conclusion_critical_kernel_one_target_denominator_reconstruction_denominatorCoeff j =
        (j + conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) *
          conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff j
  conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv_mul :
    conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv *
      conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff
        conclusion_critical_kernel_one_target_denominator_reconstruction_degree = 1
  conclusion_critical_kernel_one_target_denominator_reconstruction_nonzeroFactor :
    ∀ j : ℕ, (j + conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) ≠ 0
  conclusion_critical_kernel_one_target_denominator_reconstruction_targetParameter_formula :
    conclusion_critical_kernel_one_target_denominator_reconstruction_targetParameter =
      conclusion_critical_kernel_one_target_denominator_reconstruction_kappa +
        (1 -
          conclusion_critical_kernel_one_target_denominator_reconstruction_remainingReciprocalSum)⁻¹
  conclusion_critical_kernel_one_target_denominator_reconstruction_distribution_formula :
    ∀ x : ℕ,
      conclusion_critical_kernel_one_target_denominator_reconstruction_distribution x =
        (conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x)⁻¹ ^ 2 /
          conclusion_critical_kernel_one_target_denominator_reconstruction_distributionNormalizer

namespace conclusion_critical_kernel_one_target_denominator_reconstruction_data

/-- The leading denominator coefficient reconstructs the Laguerre shift `κ`. -/
def recoversKappa
    (D : conclusion_critical_kernel_one_target_denominator_reconstruction_data) : Prop :=
  D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa =
    D.conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv *
      D.conclusion_critical_kernel_one_target_denominator_reconstruction_denominatorCoeff
        D.conclusion_critical_kernel_one_target_denominator_reconstruction_degree -
      D.conclusion_critical_kernel_one_target_denominator_reconstruction_degree

/-- After `κ` is known, each coefficient of `P_{-y}` is obtained by division. -/
def recoversPminusY
    (D : conclusion_critical_kernel_one_target_denominator_reconstruction_data) : Prop :=
  ∀ j : ℕ,
    D.conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff j =
      D.conclusion_critical_kernel_one_target_denominator_reconstruction_denominatorCoeff j /
        (j + D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa)

/-- The missing target parameter is recovered from the normalization equation. -/
def recoversTargetParameter
    (D : conclusion_critical_kernel_one_target_denominator_reconstruction_data) : Prop :=
  D.conclusion_critical_kernel_one_target_denominator_reconstruction_targetParameter =
    D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa +
      (1 -
        D.conclusion_critical_kernel_one_target_denominator_reconstruction_remainingReciprocalSum)⁻¹

/-- The recovered parameter family determines the distribution by the normalized inverse-square law. -/
def recoversDistribution
    (D : conclusion_critical_kernel_one_target_denominator_reconstruction_data) : Prop :=
  ∀ x : ℕ,
    D.conclusion_critical_kernel_one_target_denominator_reconstruction_distribution x =
      (D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x)⁻¹ ^ 2 /
        D.conclusion_critical_kernel_one_target_denominator_reconstruction_distributionNormalizer

end conclusion_critical_kernel_one_target_denominator_reconstruction_data

/-- Paper label: `thm:conclusion-critical-kernel-one-target-denominator-reconstruction`. -/
theorem paper_conclusion_critical_kernel_one_target_denominator_reconstruction
    (h : conclusion_critical_kernel_one_target_denominator_reconstruction_data) :
    h.recoversKappa ∧ h.recoversPminusY ∧ h.recoversTargetParameter ∧
      h.recoversDistribution := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [conclusion_critical_kernel_one_target_denominator_reconstruction_data.recoversKappa]
    have hcoeff :=
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_coeffCompare
        h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree
    have hlead :=
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv_mul
    rw [hcoeff]
    calc
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa =
          (h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree +
              h.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) *
            (h.conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv *
              h.conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff
                h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree) -
            h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree := by
            rw [hlead]
            ring
      _ =
          h.conclusion_critical_kernel_one_target_denominator_reconstruction_leadingCoeffInv *
              ((h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree +
                  h.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) *
                h.conclusion_critical_kernel_one_target_denominator_reconstruction_polynomialCoeff
                  h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree) -
            h.conclusion_critical_kernel_one_target_denominator_reconstruction_degree := by
            ring
  · rw [conclusion_critical_kernel_one_target_denominator_reconstruction_data.recoversPminusY]
    intro j
    have hcoeff :=
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_coeffCompare j
    have hnonzero :=
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_nonzeroFactor j
    rw [hcoeff]
    field_simp [hnonzero]
  · exact
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_targetParameter_formula
  · exact
      h.conclusion_critical_kernel_one_target_denominator_reconstruction_distribution_formula

end

end Omega.Conclusion
