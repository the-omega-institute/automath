import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeCoboundary

namespace Omega.SyncKernelWeighted

open Matrix

/-- The reduced one-state potential extracted from the audited real-input-40 charge potential. -/
def prop_real_input_40_arity_charge_similarity_reduction_reduced_potential : Fin 1 → ℤ
  | _ => realInput40ArityChargePotential 0

/-- The diagonal conjugator associated with the reduced potential. -/
def prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator :
    Matrix (Fin 1) (Fin 1) ℤ :=
  Matrix.diagonal fun i =>
    if prop_real_input_40_arity_charge_similarity_reduction_reduced_potential i = -1 then
      (-1 : ℤ)
    else
      1

/-- The diagonal normal form used as the reduced base block. -/
def prop_real_input_40_arity_charge_similarity_reduction_base_matrix :
    Matrix (Fin 1) (Fin 1) ℤ :=
  !![(1 : ℤ)]

/-- The charge-twisted block obtained by diagonal conjugation from the reduced normal form. -/
def prop_real_input_40_arity_charge_similarity_reduction_charge_matrix :
    Matrix (Fin 1) (Fin 1) ℤ :=
  prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator *
    prop_real_input_40_arity_charge_similarity_reduction_base_matrix *
    prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator

/-- Paper-facing reduced similarity statement: the coboundary package is available, the diagonal
conjugator gives the entrywise reduction, and determinant/trace are unchanged on the reduced
block. -/
def real_input_40_arity_charge_similarity_reduction_statement
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) : Prop :=
  D.coboundaryNormalization ∧
    D.edgeAuditWithPotential ∧
    D.primitiveCycleDensityBound ∧
    prop_real_input_40_arity_charge_similarity_reduction_charge_matrix =
      prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator *
        prop_real_input_40_arity_charge_similarity_reduction_base_matrix *
        prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator ∧
    (∀ i j,
      prop_real_input_40_arity_charge_similarity_reduction_charge_matrix i j =
        (prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator i i) *
          (prop_real_input_40_arity_charge_similarity_reduction_base_matrix i j) *
          (prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator j j)) ∧
    Matrix.det prop_real_input_40_arity_charge_similarity_reduction_charge_matrix =
      Matrix.det prop_real_input_40_arity_charge_similarity_reduction_base_matrix ∧
    Matrix.trace prop_real_input_40_arity_charge_similarity_reduction_charge_matrix =
      Matrix.trace prop_real_input_40_arity_charge_similarity_reduction_base_matrix

/-- Paper label: `prop:real-input-40-arity-charge-similarity-reduction`. The existing coboundary
certificate supplies the normalization/audit package; on the reduced one-state quotient the
audited potential defines a diagonal conjugator, and the charge block is visibly similar to the
normal-form block, so determinant and trace agree. -/
theorem paper_real_input_40_arity_charge_similarity_reduction
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) :
    real_input_40_arity_charge_similarity_reduction_statement D := by
  rcases paper_real_input_40_arity_charge_coboundary D with ⟨hNorm, hAudit, hBound⟩
  have hpot : realInput40ArityChargePotential 0 = -1 := rfl
  refine ⟨hNorm, hAudit, hBound, rfl, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i
    fin_cases j
    simp [prop_real_input_40_arity_charge_similarity_reduction_charge_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator,
      prop_real_input_40_arity_charge_similarity_reduction_base_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_reduced_potential, Matrix.mul_apply,
      hpot]
  · simp [prop_real_input_40_arity_charge_similarity_reduction_charge_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator,
      prop_real_input_40_arity_charge_similarity_reduction_base_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_reduced_potential, Matrix.mul_apply,
      hpot]
  · simp [prop_real_input_40_arity_charge_similarity_reduction_charge_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_diagonal_conjugator,
      prop_real_input_40_arity_charge_similarity_reduction_base_matrix,
      prop_real_input_40_arity_charge_similarity_reduction_reduced_potential,
      Matrix.trace_fin_one, Matrix.mul_apply, hpot]

end Omega.SyncKernelWeighted
