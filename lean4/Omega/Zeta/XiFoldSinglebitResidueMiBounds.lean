import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data package for the single-bit residue mutual-information bounds.

The fields record the entropy identity, the linearity/monotonicity facts needed to pass scalar
binary-entropy bounds through expectation, and the chi-square identification. -/
structure xi_fold_singlebit_residue_mi_bounds_data where
  mutualInformation : ℝ
  expectation : (ℝ → ℝ) → ℝ
  binaryEntropy : ℝ → ℝ
  beta : ℝ → ℝ
  chiSquare : ℝ
  mutualInformation_entropy_identity :
    mutualInformation =
      Real.log 2 - expectation (fun r => binaryEntropy ((1 + beta r) / 2))
  expectation_sub_const :
    Real.log 2 - expectation (fun r => binaryEntropy ((1 + beta r) / 2)) =
      expectation (fun r => Real.log 2 - binaryEntropy ((1 + beta r) / 2))
  expectation_half_mul :
    expectation (fun r => (1 / 2 : ℝ) * (beta r) ^ 2) =
      (1 / 2 : ℝ) * expectation (fun r => (beta r) ^ 2)
  expectation_neg_half_mul :
    expectation (fun r => -(1 / 2 : ℝ) * Real.log (1 - (beta r) ^ 2)) =
      -(1 / 2 : ℝ) * expectation (fun r => Real.log (1 - (beta r) ^ 2))
  expectation_mono :
    ∀ {f g : ℝ → ℝ}, (∀ r, f r ≤ g r) → expectation f ≤ expectation g
  binaryEntropy_gap_lower :
    ∀ r, (1 / 2 : ℝ) * (beta r) ^ 2 ≤
      Real.log 2 - binaryEntropy ((1 + beta r) / 2)
  binaryEntropy_gap_upper :
    ∀ r, Real.log 2 - binaryEntropy ((1 + beta r) / 2) ≤
      -(1 / 2 : ℝ) * Real.log (1 - (beta r) ^ 2)
  chiSquare_identity :
    expectation (fun r => (beta r) ^ 2) = chiSquare

/-- Paper label: `thm:xi-fold-singlebit-residue-mi-bounds`. -/
theorem paper_xi_fold_singlebit_residue_mi_bounds
    (D : xi_fold_singlebit_residue_mi_bounds_data) :
    D.mutualInformation =
        Real.log 2 - D.expectation (fun r => D.binaryEntropy ((1 + D.beta r) / 2)) ∧
      (1 / 2 : ℝ) * D.expectation (fun r => (D.beta r) ^ 2) ≤ D.mutualInformation ∧
      D.mutualInformation ≤
        -(1 / 2 : ℝ) * D.expectation (fun r => Real.log (1 - (D.beta r) ^ 2)) ∧
      D.expectation (fun r => (D.beta r) ^ 2) = D.chiSquare := by
  refine ⟨D.mutualInformation_entropy_identity, ?_, ?_, D.chiSquare_identity⟩
  · have hscalar :
        D.expectation (fun r => (1 / 2 : ℝ) * (D.beta r) ^ 2) ≤
          D.expectation
            (fun r => Real.log 2 - D.binaryEntropy ((1 + D.beta r) / 2)) :=
      D.expectation_mono (fun r => D.binaryEntropy_gap_lower r)
    have hgap :
        (1 / 2 : ℝ) * D.expectation (fun r => (D.beta r) ^ 2) ≤
          Real.log 2 - D.expectation (fun r => D.binaryEntropy ((1 + D.beta r) / 2)) := by
      rw [D.expectation_half_mul] at hscalar
      simpa [D.expectation_sub_const] using hscalar
    simpa [D.mutualInformation_entropy_identity] using hgap
  · have hscalar :
        D.expectation
            (fun r => Real.log 2 - D.binaryEntropy ((1 + D.beta r) / 2)) ≤
          D.expectation
            (fun r => -(1 / 2 : ℝ) * Real.log (1 - (D.beta r) ^ 2)) :=
      D.expectation_mono (fun r => D.binaryEntropy_gap_upper r)
    have hgap :
        Real.log 2 - D.expectation (fun r => D.binaryEntropy ((1 + D.beta r) / 2)) ≤
          -(1 / 2 : ℝ) * D.expectation (fun r => Real.log (1 - (D.beta r) ^ 2)) := by
      rw [D.expectation_neg_half_mul] at hscalar
      simpa [D.expectation_sub_const] using hscalar
    simpa [D.mutualInformation_entropy_identity] using hgap

end Omega.Zeta
