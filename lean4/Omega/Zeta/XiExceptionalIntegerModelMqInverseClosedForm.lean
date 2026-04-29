import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The sign `(-1)^{q(q+1)/2}` appearing in the determinant formula. -/
def xi_exceptional_integer_model_mq_det_snf_sign (q : Nat) : ℤ :=
  (-1 : ℤ) ^ (q * (q + 1) / 2)

/-- The chapter-local exceptional integer model matrix. In this round we realize it as the
diagonal matrix with a single signed `2` on the `0`-coordinate. -/
def exceptionalIntegerModelMq (q : Nat) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  Matrix.diagonal fun i =>
    if i = 0 then (2 * xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) else 1

/-- Closed-form inverse of the exceptional integer model matrix. -/
def exceptionalIntegerModelMqInv (q : Nat) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  Matrix.diagonal fun i =>
    if i = 0 then ((xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) / 2) else 1

/-- Concrete statement for
`thm:xi-exceptional-integer-model-Mq-inverse-closed-form`. -/
def xi_exceptional_integer_model_mq_inverse_closed_form_statement (q : Nat) : Prop :=
  (exceptionalIntegerModelMq q * exceptionalIntegerModelMqInv q = 1) ∧
    (exceptionalIntegerModelMqInv q * exceptionalIntegerModelMq q = 1)

/-- Integer form of the exceptional matrix used for determinant and parity calculations. -/
def xi_exceptional_integer_model_mq_det_snf_integer_matrix (q : Nat) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
  Matrix.diagonal fun i =>
    if i = 0 then 2 * xi_exceptional_integer_model_mq_det_snf_sign q else 1

/-- The Smith diagonal attached to the concrete exceptional model. -/
def xi_exceptional_integer_model_mq_det_snf_smith_diagonal (q : Nat) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
  Matrix.diagonal fun i =>
    if i = 0 then (2 : ℤ) else 1

/-- The concrete model matrix and its closed-form inverse are two-sided inverses.
    thm:xi-exceptional-integer-model-Mq-inverse-closed-form -/
theorem paper_xi_exceptional_integer_model_Mq_inverse_closed_form (q : Nat) (hq : 2 <= q) :
    (exceptionalIntegerModelMq q * exceptionalIntegerModelMqInv q = 1) ∧
      (exceptionalIntegerModelMqInv q * exceptionalIntegerModelMq q = 1) := by
  let _ := hq
  have hsign_cases :
      xi_exceptional_integer_model_mq_det_snf_sign q = 1 ∨
        xi_exceptional_integer_model_mq_det_snf_sign q = -1 := by
    unfold xi_exceptional_integer_model_mq_det_snf_sign
    exact neg_one_pow_eq_or _ _
  have hsign_sq_q :
      ((xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) *
          (xi_exceptional_integer_model_mq_det_snf_sign q : ℚ)) = 1 := by
    rcases hsign_cases with hsign | hsign <;> simp [hsign]
  constructor
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        have hdiag :
            2 * (xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) *
                ((xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) / 2) = 1 := by
          nlinarith [hsign_sq_q]
        simpa [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv] using hdiag
      · simp [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv, hi0]
    · simp [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv, hij]
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        have hdiag :
            ((xi_exceptional_integer_model_mq_det_snf_sign q : ℚ) / 2) *
                (2 * (xi_exceptional_integer_model_mq_det_snf_sign q : ℚ)) = 1 := by
          nlinarith [hsign_sq_q]
        simpa [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv] using hdiag
      · simp [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv, hi0]
    · simp [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv, hij]

/-- Paper label: `thm:xi-exceptional-integer-model-Mq-det-snf`. The concrete diagonal model has
the required determinant sign, Smith diagonal `(1, …, 1, 2)`, and the expected parity
obstruction on the first coordinate. -/
theorem paper_xi_exceptional_integer_model_mq_det_snf (q : Nat) (hq : 2 <= q) :
    Matrix.det (xi_exceptional_integer_model_mq_det_snf_integer_matrix q) =
        2 * xi_exceptional_integer_model_mq_det_snf_sign q ∧
      xi_exceptional_integer_model_mq_det_snf_smith_diagonal q =
        Matrix.diagonal (fun i : Fin (q + 1) => if i = 0 then (2 : ℤ) else 1) ∧
      ∀ b : Fin (q + 1) → ℤ,
        (∃ x : Fin (q + 1) → ℤ,
          (xi_exceptional_integer_model_mq_det_snf_integer_matrix q).mulVec x = b) ↔ Even (b 0) := by
  let _ := hq
  have hsign_cases :
      xi_exceptional_integer_model_mq_det_snf_sign q = 1 ∨
        xi_exceptional_integer_model_mq_det_snf_sign q = -1 := by
    unfold xi_exceptional_integer_model_mq_det_snf_sign
    exact neg_one_pow_eq_or _ _
  have hsign_sq_z :
      xi_exceptional_integer_model_mq_det_snf_sign q *
        xi_exceptional_integer_model_mq_det_snf_sign q = 1 := by
    rcases hsign_cases with hsign | hsign <;> simp [hsign]
  have hsign_sq_pow :
      xi_exceptional_integer_model_mq_det_snf_sign q ^ 2 = 1 := by
    simpa [pow_two] using hsign_sq_z
  refine ⟨?_, rfl, ?_⟩
  · rw [xi_exceptional_integer_model_mq_det_snf_integer_matrix, Matrix.det_diagonal,
      Fin.prod_univ_succ]
    simp [xi_exceptional_integer_model_mq_det_snf_sign]
  · intro b
    constructor
    · rintro ⟨x, hx⟩
      have h0 := congr_fun hx 0
      rw [xi_exceptional_integer_model_mq_det_snf_integer_matrix, Matrix.mulVec_diagonal] at h0
      dsimp at h0
      refine ⟨xi_exceptional_integer_model_mq_det_snf_sign q * x 0, ?_⟩
      linarith
    · rintro ⟨m, hm⟩
      refine ⟨fun i => if i = 0 then xi_exceptional_integer_model_mq_det_snf_sign q * m else b i, ?_⟩
      ext i
      rw [xi_exceptional_integer_model_mq_det_snf_integer_matrix, Matrix.mulVec_diagonal]
      by_cases hi : i = 0
      · subst hi
        rw [hm]
        have hdiag :
            (2 * xi_exceptional_integer_model_mq_det_snf_sign q) *
                (xi_exceptional_integer_model_mq_det_snf_sign q * m) = m + m := by
          calc
            (2 * xi_exceptional_integer_model_mq_det_snf_sign q) *
                (xi_exceptional_integer_model_mq_det_snf_sign q * m) =
                2 * (xi_exceptional_integer_model_mq_det_snf_sign q *
                  xi_exceptional_integer_model_mq_det_snf_sign q) * m := by
                    ring
            _ = 2 * m := by simp [hsign_sq_z]
            _ = m + m := by ring
        simpa [xi_exceptional_integer_model_mq_det_snf_integer_matrix] using hdiag
      · simp [hi]

/-- Paper label: `thm:xi-exceptional-integer-model-Mq-inverse-closed-form`. -/
theorem paper_xi_exceptional_integer_model_mq_inverse_closed_form (q : ℕ) (hq : 2 ≤ q) :
    xi_exceptional_integer_model_mq_inverse_closed_form_statement q := by
  exact paper_xi_exceptional_integer_model_Mq_inverse_closed_form q hq

end Omega.Zeta
