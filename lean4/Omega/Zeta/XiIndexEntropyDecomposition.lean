import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite data for the integer-index and defect-entropy decomposition. -/
structure xi_index_entropy_decomposition_data where
  xi_index_entropy_decomposition_defectCount : ℕ
  xi_index_entropy_decomposition_integerIndex : ℤ
  xi_index_entropy_decomposition_windingIndexMass : ℚ
  xi_index_entropy_decomposition_defectMultiplicity :
    Fin xi_index_entropy_decomposition_defectCount → ℚ
  xi_index_entropy_decomposition_defectDelta :
    Fin xi_index_entropy_decomposition_defectCount → ℚ
  xi_index_entropy_decomposition_delta_den_ne :
    ∀ j, 1 + xi_index_entropy_decomposition_defectDelta j ≠ 0
  xi_index_entropy_decomposition_windingIndexMass_eq :
    xi_index_entropy_decomposition_windingIndexMass =
      (xi_index_entropy_decomposition_integerIndex : ℚ) +
        ∑ j, xi_index_entropy_decomposition_defectMultiplicity j

namespace xi_index_entropy_decomposition_data

/-- The finite defect entropy contribution before the closed-form rewrite. -/
def xi_index_entropy_decomposition_defectEntropy
    (D : xi_index_entropy_decomposition_data) : ℚ :=
  ∑ j,
    D.xi_index_entropy_decomposition_defectMultiplicity j *
      (D.xi_index_entropy_decomposition_defectDelta j /
        (1 + D.xi_index_entropy_decomposition_defectDelta j))

/-- The closed-form entropy invariant after rewriting each defect term. -/
def xi_index_entropy_decomposition_closedFormEntropyInvariant
    (D : xi_index_entropy_decomposition_data) : ℚ :=
  ∑ j,
    D.xi_index_entropy_decomposition_defectMultiplicity j *
      (1 - (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹)

/-- Integer index plus raw defect entropy. -/
def xi_index_entropy_decomposition_totalIndexEntropy
    (D : xi_index_entropy_decomposition_data) : ℚ :=
  (D.xi_index_entropy_decomposition_integerIndex : ℚ) +
    D.xi_index_entropy_decomposition_defectEntropy

/-- Concrete statement: the raw finite entropy sum has the closed form, and the total index
entropy decomposes as winding-index mass minus the residual reciprocal defect terms. -/
def xi_index_entropy_decomposition_statement
    (D : xi_index_entropy_decomposition_data) : Prop :=
  D.xi_index_entropy_decomposition_defectEntropy =
      D.xi_index_entropy_decomposition_closedFormEntropyInvariant ∧
    D.xi_index_entropy_decomposition_totalIndexEntropy =
      D.xi_index_entropy_decomposition_windingIndexMass -
        ∑ j,
          D.xi_index_entropy_decomposition_defectMultiplicity j *
            (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹

lemma xi_index_entropy_decomposition_delta_fraction_identity
    (D : xi_index_entropy_decomposition_data)
    (j : Fin D.xi_index_entropy_decomposition_defectCount) :
    D.xi_index_entropy_decomposition_defectDelta j /
        (1 + D.xi_index_entropy_decomposition_defectDelta j) =
      1 - (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹ := by
  field_simp [D.xi_index_entropy_decomposition_delta_den_ne j]
  ring

lemma xi_index_entropy_decomposition_defectEntropy_closed
    (D : xi_index_entropy_decomposition_data) :
    D.xi_index_entropy_decomposition_defectEntropy =
      D.xi_index_entropy_decomposition_closedFormEntropyInvariant := by
  unfold xi_index_entropy_decomposition_defectEntropy
    xi_index_entropy_decomposition_closedFormEntropyInvariant
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [xi_index_entropy_decomposition_delta_fraction_identity D j]

lemma xi_index_entropy_decomposition_closedForm_sum_sub
    (D : xi_index_entropy_decomposition_data) :
    D.xi_index_entropy_decomposition_closedFormEntropyInvariant =
      (∑ j, D.xi_index_entropy_decomposition_defectMultiplicity j) -
        ∑ j,
          D.xi_index_entropy_decomposition_defectMultiplicity j *
            (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹ := by
  unfold xi_index_entropy_decomposition_closedFormEntropyInvariant
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

end xi_index_entropy_decomposition_data

open xi_index_entropy_decomposition_data

/-- Paper label: `prop:xi-index-entropy-decomposition`. -/
theorem paper_xi_index_entropy_decomposition (D : xi_index_entropy_decomposition_data) :
    xi_index_entropy_decomposition_statement D := by
  constructor
  · exact xi_index_entropy_decomposition_defectEntropy_closed D
  · calc
      D.xi_index_entropy_decomposition_totalIndexEntropy =
          (D.xi_index_entropy_decomposition_integerIndex : ℚ) +
            D.xi_index_entropy_decomposition_closedFormEntropyInvariant := by
            rw [xi_index_entropy_decomposition_totalIndexEntropy,
              xi_index_entropy_decomposition_defectEntropy_closed D]
      _ =
          (D.xi_index_entropy_decomposition_integerIndex : ℚ) +
            ((∑ j, D.xi_index_entropy_decomposition_defectMultiplicity j) -
              ∑ j,
                D.xi_index_entropy_decomposition_defectMultiplicity j *
                  (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹) := by
            rw [xi_index_entropy_decomposition_closedForm_sum_sub D]
      _ =
          D.xi_index_entropy_decomposition_windingIndexMass -
            ∑ j,
              D.xi_index_entropy_decomposition_defectMultiplicity j *
                (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹ := by
            rw [D.xi_index_entropy_decomposition_windingIndexMass_eq]
            ring

/-- Paper label: `con:xi-index-entropy-strict-separation`. The finite defect entropy separates
as the raw integer multiplicity sum minus the reciprocal depth penalty. -/
theorem paper_xi_index_entropy_strict_separation (D : xi_index_entropy_decomposition_data) :
    D.xi_index_entropy_decomposition_defectEntropy =
      (∑ j, D.xi_index_entropy_decomposition_defectMultiplicity j) -
        ∑ j,
          D.xi_index_entropy_decomposition_defectMultiplicity j *
            (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹ := by
  calc
    D.xi_index_entropy_decomposition_defectEntropy =
        D.xi_index_entropy_decomposition_closedFormEntropyInvariant := by
        exact xi_index_entropy_decomposition_defectEntropy_closed D
    _ =
        (∑ j, D.xi_index_entropy_decomposition_defectMultiplicity j) -
          ∑ j,
            D.xi_index_entropy_decomposition_defectMultiplicity j *
              (1 + D.xi_index_entropy_decomposition_defectDelta j)⁻¹ := by
        exact xi_index_entropy_decomposition_closedForm_sum_sub D

end Omega.Zeta
