import Omega.Zeta.XiExceptionalIntegerModelMqInverseClosedForm

namespace Omega.Zeta

open Matrix

/-- The diagonal inverse part before removing the exceptional `(0,0)` half-entry. -/
def xi_exceptional_integer_model_mq_rank1_decomposition_inverse_part (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  Matrix.diagonal fun i =>
    if i = 0 then
      ((xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) + 1) / 2
    else 1

/-- The matrix unit supported at the exceptional `(0,0)` coordinate. -/
def xi_exceptional_integer_model_mq_rank1_decomposition_e00 (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  Matrix.diagonal fun i => if i = 0 then 1 else 0

/-- The forward diagonal part after extracting the exceptional rank-one coordinate. -/
def xi_exceptional_integer_model_mq_rank1_decomposition_forward_part (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  Matrix.diagonal fun i =>
    if i = 0 then
      (2 * xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) - 1
    else 1

/-- The rank-one correction at the exceptional coordinate. -/
def xi_exceptional_integer_model_mq_rank1_decomposition_rank_one_part (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  xi_exceptional_integer_model_mq_rank1_decomposition_e00 q

/-- Paper label: `prop:xi-exceptional-integer-model-Mq-rank1-decomposition`. -/
theorem paper_xi_exceptional_integer_model_mq_rank1_decomposition (q : ℕ) (hq : 2 ≤ q) :
    exceptionalIntegerModelMqInv q =
        xi_exceptional_integer_model_mq_rank1_decomposition_inverse_part q -
          (1 / 2 : ℚ) • xi_exceptional_integer_model_mq_rank1_decomposition_e00 q ∧
      exceptionalIntegerModelMq q =
        xi_exceptional_integer_model_mq_rank1_decomposition_forward_part q +
          xi_exceptional_integer_model_mq_rank1_decomposition_rank_one_part q := by
  let _ := hq
  constructor
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        simp [exceptionalIntegerModelMqInv,
          xi_exceptional_integer_model_mq_rank1_decomposition_inverse_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_e00]
        ring
      · simp [exceptionalIntegerModelMqInv,
          xi_exceptional_integer_model_mq_rank1_decomposition_inverse_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_e00, hi0]
    · simp [exceptionalIntegerModelMqInv,
        xi_exceptional_integer_model_mq_rank1_decomposition_inverse_part,
        xi_exceptional_integer_model_mq_rank1_decomposition_e00, hij]
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        simp [exceptionalIntegerModelMq,
          xi_exceptional_integer_model_mq_rank1_decomposition_forward_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_rank_one_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_e00]
      · simp [exceptionalIntegerModelMq,
          xi_exceptional_integer_model_mq_rank1_decomposition_forward_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_rank_one_part,
          xi_exceptional_integer_model_mq_rank1_decomposition_e00, hi0]
    · simp [exceptionalIntegerModelMq,
        xi_exceptional_integer_model_mq_rank1_decomposition_forward_part,
        xi_exceptional_integer_model_mq_rank1_decomposition_rank_one_part,
        xi_exceptional_integer_model_mq_rank1_decomposition_e00, hij]

end Omega.Zeta
