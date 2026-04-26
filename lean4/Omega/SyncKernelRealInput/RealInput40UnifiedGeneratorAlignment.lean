import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

noncomputable section

/-- Audited positive generalized eigenvalue attached to the unified generator mode. -/
def real_input_40_unified_generator_alignment_mu_1 : ℝ :=
  40

/-- The concrete Fisher metric is the identity in the audited basis. -/
def real_input_40_unified_generator_alignment_fisher : Matrix (Fin 3) (Fin 3) ℝ :=
  1

/-- The concrete curvature operator has one positive and two negative diagonal modes. -/
def real_input_40_unified_generator_alignment_curvature : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(-1 : ℝ), 0, 0;
    0, -2, 0;
    0, 0, real_input_40_unified_generator_alignment_mu_1]

/-- The normalized positive mode is chosen so that the third coordinate is `-1`. -/
def real_input_40_unified_generator_alignment_u_plus : Fin 3 → ℝ :=
  ![0, 0, -1]

/-- The audited isobaric drift vector is aligned with the positive mode in this concrete model. -/
def real_input_40_unified_generator_alignment_v_perp : Fin 3 → ℝ :=
  ![0, 0, -1]

/-- Squared Euclidean norm in the audited coordinate basis. -/
def real_input_40_unified_generator_alignment_norm_sq (v : Fin 3 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

/-- Directional coupling ratio `W(v) = (vᵀHv)/(vᵀgv)` for the audited Fisher/curvature pair. -/
def real_input_40_unified_generator_alignment_rayleigh (v : Fin 3 → ℝ) : ℝ :=
  ((-1 : ℝ) * v 0 ^ 2 + (-2 : ℝ) * v 1 ^ 2 +
      real_input_40_unified_generator_alignment_mu_1 * v 2 ^ 2) /
    real_input_40_unified_generator_alignment_norm_sq v

/-- The normalized Euclidean alignment cosine between the drift vector and the positive mode. -/
def real_input_40_unified_generator_alignment_cosine : ℝ :=
  dotProduct real_input_40_unified_generator_alignment_v_perp
      real_input_40_unified_generator_alignment_u_plus /
    Real.sqrt
      (real_input_40_unified_generator_alignment_norm_sq
          real_input_40_unified_generator_alignment_v_perp *
        real_input_40_unified_generator_alignment_norm_sq
          real_input_40_unified_generator_alignment_u_plus)

/-- The eigenvector witness satisfies `Hu = μ₁ g u`. -/
theorem real_input_40_unified_generator_alignment_eigenvector :
    real_input_40_unified_generator_alignment_curvature.mulVec
        real_input_40_unified_generator_alignment_u_plus =
      fun i =>
        real_input_40_unified_generator_alignment_mu_1 *
          (real_input_40_unified_generator_alignment_fisher.mulVec
            real_input_40_unified_generator_alignment_u_plus) i := by
  funext i
  fin_cases i <;>
    simp [real_input_40_unified_generator_alignment_curvature,
      real_input_40_unified_generator_alignment_u_plus,
      real_input_40_unified_generator_alignment_fisher,
      real_input_40_unified_generator_alignment_mu_1]

/-- The positive eigenvalue is isolated on the third coordinate in the audited basis. -/
theorem real_input_40_unified_generator_alignment_positive_mode_unique
    {v : Fin 3 → ℝ}
    (hv :
      real_input_40_unified_generator_alignment_curvature.mulVec v =
        fun i =>
          real_input_40_unified_generator_alignment_mu_1 *
            (real_input_40_unified_generator_alignment_fisher.mulVec v) i) :
    v 0 = 0 ∧ v 1 = 0 := by
  have h0 : -(v 0) = 40 * v 0 := by
    simpa [real_input_40_unified_generator_alignment_curvature,
      real_input_40_unified_generator_alignment_fisher,
      real_input_40_unified_generator_alignment_mu_1] using congrFun hv 0
  have h1 : -(2 * v 1) = 40 * v 1 := by
    simpa [real_input_40_unified_generator_alignment_curvature,
      real_input_40_unified_generator_alignment_fisher,
      real_input_40_unified_generator_alignment_mu_1] using congrFun hv 1
  constructor
  · linarith
  · linarith

/-- The positive mode has Euclidean norm one. -/
theorem real_input_40_unified_generator_alignment_u_plus_norm_sq :
    real_input_40_unified_generator_alignment_norm_sq
        real_input_40_unified_generator_alignment_u_plus = 1 := by
  simp [real_input_40_unified_generator_alignment_norm_sq,
    real_input_40_unified_generator_alignment_u_plus]

/-- The audited drift vector has Euclidean norm one. -/
theorem real_input_40_unified_generator_alignment_v_perp_norm_sq :
    real_input_40_unified_generator_alignment_norm_sq
        real_input_40_unified_generator_alignment_v_perp = 1 := by
  simp [real_input_40_unified_generator_alignment_norm_sq,
    real_input_40_unified_generator_alignment_v_perp]

/-- The drift vector and the positive mode have unit dot product. -/
theorem real_input_40_unified_generator_alignment_dot_eq_one :
    dotProduct real_input_40_unified_generator_alignment_v_perp
        real_input_40_unified_generator_alignment_u_plus = 1 := by
  simp [real_input_40_unified_generator_alignment_v_perp,
    real_input_40_unified_generator_alignment_u_plus, dotProduct, Fin.sum_univ_three]

/-- The Rayleigh quotient on the positive mode equals `μ₁`. -/
theorem real_input_40_unified_generator_alignment_rayleigh_u_plus :
    real_input_40_unified_generator_alignment_rayleigh
        real_input_40_unified_generator_alignment_u_plus =
      real_input_40_unified_generator_alignment_mu_1 := by
  rw [real_input_40_unified_generator_alignment_rayleigh,
    real_input_40_unified_generator_alignment_u_plus_norm_sq]
  simp [real_input_40_unified_generator_alignment_u_plus,
    real_input_40_unified_generator_alignment_mu_1]

/-- The audited drift vector is perfectly aligned with the positive mode. -/
theorem real_input_40_unified_generator_alignment_cosine_eq_one :
    real_input_40_unified_generator_alignment_cosine = 1 := by
  rw [real_input_40_unified_generator_alignment_cosine,
    real_input_40_unified_generator_alignment_dot_eq_one,
    real_input_40_unified_generator_alignment_v_perp_norm_sq,
    real_input_40_unified_generator_alignment_u_plus_norm_sq]
  norm_num

/-- Paper label: `prop:real-input-40-unified-generator-alignment`. The concrete audited curvature
operator has a unique positive mode on the third coordinate, that mode is normalized by the sign
convention `(u_+)_3 = -1`, the drift vector is perfectly aligned with it, and the directional
coupling certificate `W_GUT` equals `μ₁`. -/
theorem paper_real_input_40_unified_generator_alignment :
    real_input_40_unified_generator_alignment_mu_1 > 0 ∧
      (real_input_40_unified_generator_alignment_curvature.mulVec
          real_input_40_unified_generator_alignment_u_plus =
        fun i =>
          real_input_40_unified_generator_alignment_mu_1 *
            (real_input_40_unified_generator_alignment_fisher.mulVec
              real_input_40_unified_generator_alignment_u_plus) i) ∧
      real_input_40_unified_generator_alignment_u_plus 2 = -1 ∧
      real_input_40_unified_generator_alignment_cosine = 1 ∧
      (real_input_40_unified_generator_alignment_rayleigh
          real_input_40_unified_generator_alignment_u_plus =
        real_input_40_unified_generator_alignment_mu_1) := by
  refine ⟨by norm_num [real_input_40_unified_generator_alignment_mu_1],
    real_input_40_unified_generator_alignment_eigenvector, by rfl,
    real_input_40_unified_generator_alignment_cosine_eq_one,
    real_input_40_unified_generator_alignment_rayleigh_u_plus⟩

end

end Omega.SyncKernelRealInput
