import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.Conclusion.ToeplitzGaugeBlindnessZeroDimensionalLedgerNecessity
import Omega.Zeta.ToeplitzNegativeSpectrumProductDetHankelSquare

namespace Omega.Conclusion

open Matrix
open scoped BigOperators

/-- The diagonal Hankel Gram block that records the negative Toeplitz directions in the simplified
chart used in this wrapper. -/
def toeplitzNegativeGramBlock {κ : ℕ} (σ : Fin κ → ℝ) : Matrix (Fin κ) (Fin κ) ℝ :=
  Matrix.diagonal fun i => (σ i) ^ (2 : ℕ)

/-- The explicit negative witness carried by the block `-H*H`: the quadratic form is the negative
sum of squared coordinates after the singular-value weighting. -/
def toeplitzNegativeWitness {κ : ℕ} (σ v : Fin κ → ℝ) : ℝ :=
  -∑ i, ((σ i) * (v i)) ^ (2 : ℕ)

private lemma toeplitzNegativeWitness_nonpos {κ : ℕ} (σ v : Fin κ → ℝ) :
    toeplitzNegativeWitness σ v ≤ 0 := by
  unfold toeplitzNegativeWitness
  have hsum_nonneg : 0 ≤ ∑ i, ((σ i) * (v i)) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg ((σ i) * (v i))
  linarith

private lemma toeplitzNegativeWitness_neg {κ : ℕ} (σ v : Fin κ → ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0) :
    toeplitzNegativeWitness σ v < 0 := by
  rcases hnonzero with ⟨i, hi⟩
  unfold toeplitzNegativeWitness
  have hterm_pos : 0 < ((σ i) * (v i)) ^ (2 : ℕ) := by
    exact sq_pos_iff.mpr hi
  have hsum_nonneg : 0 ≤ ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg ((σ j) * (v j))
  have hsingle :
      ((σ i) * (v i)) ^ (2 : ℕ) ≤ ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg ((σ j) * (v j))) (by simp)
  have hsum_pos : 0 < ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := lt_of_lt_of_le hterm_pos hsingle
  linarith

/-- Paper label: `thm:conclusion-toeplitz-negative-geometry-strictification-orthogonal-split`.
The negative Toeplitz block is explicitly represented by a Hankel-Gram diagonal chart, its witness
quadratic form is strictly negative whenever a weighted coordinate survives, and the strictification
shift `C ↦ C + i η` remains invisible to every audit that factors through the Carath--Pick kernel. -/
theorem paper_conclusion_toeplitz_negative_geometry_strictification_orthogonal_split
    {β : Type*} (audit : (ℂ → ℂ) → β)
    (hAudit : toeplitzAuditFactorsThroughKernel audit)
    {κ : ℕ} (σ v : Fin κ → ℝ) (C : ℂ → ℂ) (η : ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0) :
    audit (toeplitzGaugeShift C η) = audit C ∧
      (∀ w z,
        Omega.Zeta.carathPickKernel (toeplitzGaugeShift C η) w z =
          Omega.Zeta.carathPickKernel C w z) ∧
      toeplitzNegativeWitness σ v = -∑ i, ((σ i) * (v i)) ^ (2 : ℕ) ∧
      toeplitzNegativeWitness σ v < 0 ∧
      toeplitzNegativeWitness σ v ≤ 0 ∧
      (∏ i, |(-(σ i) ^ (2 : ℕ))|) = Matrix.det (toeplitzNegativeGramBlock σ) := by
  refine ⟨hAudit (carathPickKernel_toeplitzGaugeShift C η),
    carathPickKernel_toeplitzGaugeShift C η, rfl,
    toeplitzNegativeWitness_neg σ v hnonzero,
    toeplitzNegativeWitness_nonpos σ v, ?_⟩
  simpa [toeplitzNegativeGramBlock] using Omega.Zeta.paper_xi_negative_spectrum_product_dethankel_square σ

end Omega.Conclusion
