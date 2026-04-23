import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40CarryConstant
import Omega.SyncKernelWeighted.RealInput40FibTensor

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The Perron pole parameter `λ = φ²` for the audited real-input-`40` factorization. -/
def real_input_40_residue_constant_lambda : ℝ :=
  Real.goldenRatio ^ (2 : ℕ)

/-- The simple pole location `z_* = λ⁻¹ = φ⁻²`. -/
def real_input_40_residue_constant_z_star : ℝ :=
  real_input_40_residue_constant_lambda⁻¹

/-- The regular part of the determinant after factoring off the simple zero of
`1 - 3 z + z²` at `z = z_*`. -/
def real_input_40_residue_constant_regular_factor : ℝ :=
  (1 - real_input_40_residue_constant_z_star) ^ (2 : ℕ) *
    (1 + real_input_40_residue_constant_z_star) ^ (3 : ℕ) *
      (1 + real_input_40_residue_constant_z_star -
        real_input_40_residue_constant_z_star ^ (2 : ℕ))

/-- The derivative of the vanishing quadratic factor, with the sign chosen so the residue is
positive. -/
def real_input_40_residue_constant_quadratic_derivative : ℝ :=
  3 - 2 * real_input_40_residue_constant_z_star

/-- The residue constant obtained from the factored determinant and the derivative formula at the
simple pole `z = z_*`. -/
def real_input_40_residue_constant_value : ℝ :=
  real_input_40_residue_constant_lambda /
    (real_input_40_residue_constant_regular_factor *
      real_input_40_residue_constant_quadratic_derivative)

/-- The audited `z_*` matches the chapter-local carry constant and therefore equals `2 - φ`. -/
lemma real_input_40_residue_constant_z_star_eq_two_sub_phi :
    real_input_40_residue_constant_z_star = 2 - Real.goldenRatio := by
  calc
    real_input_40_residue_constant_z_star
        = Omega.SyncKernelWeighted.real_input_40_carry_constant_zStar := by
          unfold real_input_40_residue_constant_z_star real_input_40_residue_constant_lambda
            Omega.SyncKernelWeighted.real_input_40_carry_constant_zStar
          rw [inv_pow]
    _ = 2 - Real.goldenRatio := by
          exact Omega.SyncKernelWeighted.real_input_40_carry_constant_zStar_eq_two_sub_phi

/-- The residue constant simplifies to the advertised closed form in `ℚ(√5)`. -/
lemma real_input_40_residue_constant_value_eq_sqrt_form :
    real_input_40_residue_constant_value = (47 + 21 * Real.sqrt 5) / 100 := by
  have hfactorization :=
    Omega.SyncKernelWeighted.paper_real_input_40_fib_tensor
      ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData)
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ (2 : ℕ) = 5 := by
    norm_num
  have hsqrt5_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by
    positivity
  have hsqrt5_cube : (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = 5 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = (Real.sqrt 5 : ℝ) ^ (2 : ℕ) * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [hsqrt5_sq]
  have hsqrt5_four : (Real.sqrt 5 : ℝ) ^ (4 : ℕ) = 25 := by
    calc
      (Real.sqrt 5 : ℝ) ^ (4 : ℕ) = ((Real.sqrt 5 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 25 := by rw [hsqrt5_sq]; norm_num
  have hlam : (Real.goldenRatio : ℝ) ^ (2 : ℕ) = (3 + Real.sqrt 5) / 2 := by
    rw [Real.goldenRatio_sq, Real.goldenRatio]
    ring
  have hA : 1 - real_input_40_residue_constant_z_star = (Real.sqrt 5 - 1) / 2 := by
    rw [real_input_40_residue_constant_z_star_eq_two_sub_phi, Real.goldenRatio]
    ring
  have hB : 1 + real_input_40_residue_constant_z_star = (5 - Real.sqrt 5) / 2 := by
    rw [real_input_40_residue_constant_z_star_eq_two_sub_phi, Real.goldenRatio]
    ring
  have hC :
      1 + real_input_40_residue_constant_z_star -
          real_input_40_residue_constant_z_star ^ (2 : ℕ) =
        Real.sqrt 5 - 1 := by
    rw [real_input_40_residue_constant_z_star_eq_two_sub_phi, Real.goldenRatio]
    ring_nf
    rw [hsqrt5_sq]
    ring
  have hD : real_input_40_residue_constant_quadratic_derivative = Real.sqrt 5 := by
    unfold real_input_40_residue_constant_quadratic_derivative
    rw [real_input_40_residue_constant_z_star_eq_two_sub_phi, Real.goldenRatio]
    ring
  have hA2 : (((Real.sqrt 5 - 1) / 2 : ℝ) ^ (2 : ℕ)) = (3 - Real.sqrt 5) / 2 := by
    ring_nf
    rw [hsqrt5_sq]
    ring
  have hB3 : (((5 - Real.sqrt 5) / 2 : ℝ) ^ (3 : ℕ)) = 25 - 10 * Real.sqrt 5 := by
    ring_nf
    nlinarith [hsqrt5_cube]
  have hDen :
      ((3 - Real.sqrt 5) / 2 : ℝ) * (25 - 10 * Real.sqrt 5) * (Real.sqrt 5 - 1) *
          Real.sqrt 5 =
        450 - 200 * Real.sqrt 5 := by
    ring_nf
    nlinarith [hsqrt5_cube, hsqrt5_four]
  unfold real_input_40_residue_constant_value real_input_40_residue_constant_lambda
    real_input_40_residue_constant_regular_factor
    real_input_40_residue_constant_quadratic_derivative
  rw [hlam, hA, hB]
  rw [show (5 - Real.sqrt 5) / 2 - real_input_40_residue_constant_z_star ^ (2 : ℕ) =
      Real.sqrt 5 - 1 by simpa [hB] using hC]
  rw [show 3 - 2 * real_input_40_residue_constant_z_star = Real.sqrt 5 by
    simpa [real_input_40_residue_constant_quadratic_derivative] using hD]
  rw [hA2, hB3]
  rw [hDen]
  have hDen_ne : (450 - 200 * Real.sqrt 5 : ℝ) ≠ 0 := by
    nlinarith [hsqrt5_sq, hsqrt5_nonneg]
  apply (div_eq_iff hDen_ne).2
  ring_nf
  nlinarith [hsqrt5_sq, hsqrt5_nonneg]

/-- Use the known factorization of the real-input-`40` determinant, evaluate the simple-pole
residue at `z_* = φ⁻²` via the derivative formula, and simplify to the closed form.
    prop:real-input-40-residue-constant -/
theorem paper_real_input_40_residue_constant :
    real_input_40_residue_constant_value = (47 + 21 * Real.sqrt 5) / 100 ∧
      real_input_40_residue_constant_value = (13 + 21 * Real.goldenRatio) / 50 := by
  refine ⟨real_input_40_residue_constant_value_eq_sqrt_form, ?_⟩
  rw [real_input_40_residue_constant_value_eq_sqrt_form, Real.goldenRatio]
  ring

end

end Omega.SyncKernelRealInput
