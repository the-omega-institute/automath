import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Integer matrix for multiplication by `pi_phi = phi + 2` in the basis `(1, phi)`. -/
def xi_symq_golden_ar_smith_closed_form_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, 1; 1, 3]

/-- The unimodular factor appearing in `A^2 = 5 M`. -/
def xi_symq_golden_ar_smith_closed_form_unimodular_factor :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 2]

/-- The Smith exponents predicted for `A^r`. -/
def xi_symq_golden_ar_smith_closed_form_exponents (r : Nat) : Nat × Nat :=
  (r / 2, (r + 1) / 2)

/-- Concrete audited core for the closed Smith form of powers of the golden integer block. -/
def xi_symq_golden_ar_smith_closed_form_statement : Prop :=
  xi_symq_golden_ar_smith_closed_form_matrix.det = 5 ∧
    xi_symq_golden_ar_smith_closed_form_matrix ^ 2 =
      (5 : ℤ) • xi_symq_golden_ar_smith_closed_form_unimodular_factor ∧
    xi_symq_golden_ar_smith_closed_form_unimodular_factor.det = 1 ∧
    (∀ k : Nat,
      xi_symq_golden_ar_smith_closed_form_exponents (2 * k) = (k, k)) ∧
    ∀ k : Nat,
      xi_symq_golden_ar_smith_closed_form_exponents (2 * k + 1) = (k, k + 1)

/-- Paper label: `prop:xi-symq-golden-Ar-smith-closed-form`. -/
theorem paper_xi_symq_golden_ar_smith_closed_form :
    xi_symq_golden_ar_smith_closed_form_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    norm_num [xi_symq_golden_ar_smith_closed_form_matrix]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [xi_symq_golden_ar_smith_closed_form_matrix,
        xi_symq_golden_ar_smith_closed_form_unimodular_factor, pow_two, Matrix.mul_apply]
  · rw [Matrix.det_fin_two]
    norm_num [xi_symq_golden_ar_smith_closed_form_unimodular_factor]
  · intro k
    apply Prod.ext
    · simp [xi_symq_golden_ar_smith_closed_form_exponents]
    · simp [xi_symq_golden_ar_smith_closed_form_exponents]
      omega
  · intro k
    apply Prod.ext
    · simp [xi_symq_golden_ar_smith_closed_form_exponents]
      omega
    · simp [xi_symq_golden_ar_smith_closed_form_exponents]
      omega

end Omega.Zeta
