import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete adjacent residue data for recovering the zero real part from a residue ratio.
The current residue is `c * r`, the next residue is `c`, and the logarithmic real-part
formula is supplied for the recovered adjacent ratio `r`. -/
structure xi_congruence_block_residue_ratio_realpart_data where
  xi_congruence_block_residue_ratio_realpart_base : ℝ
  xi_congruence_block_residue_ratio_realpart_index : ℕ
  xi_congruence_block_residue_ratio_realpart_residue : ℕ → ℂ
  xi_congruence_block_residue_ratio_realpart_coefficient : ℂ
  xi_congruence_block_residue_ratio_realpart_ratio : ℂ
  xi_congruence_block_residue_ratio_realpart_realPart : ℝ
  xi_congruence_block_residue_ratio_realpart_current_formula :
    xi_congruence_block_residue_ratio_realpart_residue
        xi_congruence_block_residue_ratio_realpart_index =
      xi_congruence_block_residue_ratio_realpart_coefficient *
        xi_congruence_block_residue_ratio_realpart_ratio
  xi_congruence_block_residue_ratio_realpart_next_formula :
    xi_congruence_block_residue_ratio_realpart_residue
        (xi_congruence_block_residue_ratio_realpart_index + 1) =
      xi_congruence_block_residue_ratio_realpart_coefficient
  xi_congruence_block_residue_ratio_realpart_realpart_log_formula :
    xi_congruence_block_residue_ratio_realpart_realPart - (1 / 2 : ℝ) =
      -(1 / Real.log xi_congruence_block_residue_ratio_realpart_base) *
        Real.log ‖xi_congruence_block_residue_ratio_realpart_ratio‖
  xi_congruence_block_residue_ratio_realpart_half_iff_flat_ratio :
    xi_congruence_block_residue_ratio_realpart_realPart = (1 / 2 : ℝ) ↔
      ‖xi_congruence_block_residue_ratio_realpart_ratio‖ = 1

namespace xi_congruence_block_residue_ratio_realpart_data

/-- The two adjacent residues used in the quotient are nonzero. -/
def adjacentResiduesNonzero
    (D : xi_congruence_block_residue_ratio_realpart_data) : Prop :=
  D.xi_congruence_block_residue_ratio_realpart_residue
        D.xi_congruence_block_residue_ratio_realpart_index ≠ 0 ∧
    D.xi_congruence_block_residue_ratio_realpart_residue
        (D.xi_congruence_block_residue_ratio_realpart_index + 1) ≠ 0

/-- Adjacent residues cancel to the intrinsic residue ratio. -/
def ratioIdentity (D : xi_congruence_block_residue_ratio_realpart_data) : Prop :=
  D.xi_congruence_block_residue_ratio_realpart_residue
        D.xi_congruence_block_residue_ratio_realpart_index /
      D.xi_congruence_block_residue_ratio_realpart_residue
        (D.xi_congruence_block_residue_ratio_realpart_index + 1) =
    D.xi_congruence_block_residue_ratio_realpart_ratio

/-- The zero real part is recovered from the logarithmic modulus of the adjacent residue
ratio. -/
def realPartFormula (D : xi_congruence_block_residue_ratio_realpart_data) : Prop :=
  D.xi_congruence_block_residue_ratio_realpart_realPart - (1 / 2 : ℝ) =
    -(1 / Real.log D.xi_congruence_block_residue_ratio_realpart_base) *
      Real.log
        ‖D.xi_congruence_block_residue_ratio_realpart_residue
            D.xi_congruence_block_residue_ratio_realpart_index /
          D.xi_congruence_block_residue_ratio_realpart_residue
            (D.xi_congruence_block_residue_ratio_realpart_index + 1)‖

/-- Critical-line real part is equivalent to flat adjacent residue moduli. -/
def flatModulusCriterion (D : xi_congruence_block_residue_ratio_realpart_data) : Prop :=
  D.xi_congruence_block_residue_ratio_realpart_realPart = (1 / 2 : ℝ) ↔
    ‖D.xi_congruence_block_residue_ratio_realpart_residue
        D.xi_congruence_block_residue_ratio_realpart_index‖ =
      ‖D.xi_congruence_block_residue_ratio_realpart_residue
        (D.xi_congruence_block_residue_ratio_realpart_index + 1)‖

end xi_congruence_block_residue_ratio_realpart_data

open xi_congruence_block_residue_ratio_realpart_data

/-- Paper label: `cor:xi-congruence-block-residue-ratio-realpart`. -/
theorem paper_xi_congruence_block_residue_ratio_realpart
    (D : xi_congruence_block_residue_ratio_realpart_data) :
    D.adjacentResiduesNonzero →
      D.ratioIdentity ∧ D.realPartFormula ∧ D.flatModulusCriterion := by
  intro hAdjacent
  have hCoeff_ne :
      D.xi_congruence_block_residue_ratio_realpart_coefficient ≠ 0 := by
    intro hCoeff
    exact hAdjacent.2 (by
      rw [D.xi_congruence_block_residue_ratio_realpart_next_formula, hCoeff])
  have hRatio : D.ratioIdentity := by
    dsimp [ratioIdentity]
    rw [D.xi_congruence_block_residue_ratio_realpart_current_formula,
      D.xi_congruence_block_residue_ratio_realpart_next_formula]
    field_simp [hCoeff_ne]
  have hRealPart : D.realPartFormula := by
    dsimp [realPartFormula]
    rw [D.xi_congruence_block_residue_ratio_realpart_realpart_log_formula]
    rw [show D.xi_congruence_block_residue_ratio_realpart_residue
          D.xi_congruence_block_residue_ratio_realpart_index /
          D.xi_congruence_block_residue_ratio_realpart_residue
            (D.xi_congruence_block_residue_ratio_realpart_index + 1) =
        D.xi_congruence_block_residue_ratio_realpart_ratio by
      simpa [ratioIdentity] using hRatio]
  have hFlatRatio :
      ‖D.xi_congruence_block_residue_ratio_realpart_ratio‖ = 1 ↔
        ‖D.xi_congruence_block_residue_ratio_realpart_residue
            D.xi_congruence_block_residue_ratio_realpart_index‖ =
          ‖D.xi_congruence_block_residue_ratio_realpart_residue
            (D.xi_congruence_block_residue_ratio_realpart_index + 1)‖ := by
    constructor
    · intro hNorm
      rw [D.xi_congruence_block_residue_ratio_realpart_current_formula,
        D.xi_congruence_block_residue_ratio_realpart_next_formula, norm_mul, hNorm,
        mul_one]
    · intro hEq
      have hMul :
          ‖D.xi_congruence_block_residue_ratio_realpart_coefficient‖ *
              ‖D.xi_congruence_block_residue_ratio_realpart_ratio‖ =
            ‖D.xi_congruence_block_residue_ratio_realpart_coefficient‖ := by
        simpa [D.xi_congruence_block_residue_ratio_realpart_current_formula,
          D.xi_congruence_block_residue_ratio_realpart_next_formula, norm_mul] using hEq
      have hCoeff_norm_ne :
          ‖D.xi_congruence_block_residue_ratio_realpart_coefficient‖ ≠ 0 := by
        simpa [norm_eq_zero] using hCoeff_ne
      exact mul_left_cancel₀ hCoeff_norm_ne (by simpa [mul_one] using hMul)
  have hFlat : D.flatModulusCriterion := by
    dsimp [flatModulusCriterion]
    exact D.xi_congruence_block_residue_ratio_realpart_half_iff_flat_ratio.trans hFlatRatio
  exact ⟨hRatio, hRealPart, hFlat⟩

end Omega.Zeta
