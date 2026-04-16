import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic

open scoped Matrix.Norms.L2Operator

namespace Complex

/-- Local alias matching the paper-facing notation `|z|`. -/
noncomputable abbrev abs (z : ℂ) : ℝ := ‖z‖

end Complex

namespace Matrix

/-- Local alias for matrix unitarity in the L2-operator C⋆-algebra structure. -/
def IsUnitary {n : Type*} [DecidableEq n] [Fintype n] (U : Matrix n n ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup n ℂ

end Matrix

namespace Omega.Zeta

private theorem abs_eq_one_of_det_one_sub_smul_eq_zero {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.IsUnitary) :
    ∀ u : ℂ, Matrix.det (1 - u • U) = 0 → Complex.abs u = 1 := by
  intro u hu
  by_cases hu0 : u = 0
  · exfalso
    simp [hu0] at hu
  · have hfactor : (1 : Matrix (Fin n) (Fin n) ℂ) - u • U =
        u • (Matrix.scalar (Fin n) (u⁻¹) - U) := by
      have hscalar : u • Matrix.scalar (Fin n) (u⁻¹) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.scalar, hu0]
        · simp [Matrix.scalar, hij]
      calc
        (1 : Matrix (Fin n) (Fin n) ℂ) - u • U = u • Matrix.scalar (Fin n) (u⁻¹) - u • U := by
          rw [hscalar]
        _ = u • (Matrix.scalar (Fin n) (u⁻¹) - U) := by rw [smul_sub]
    have hsdet : Matrix.det (Matrix.scalar (Fin n) (u⁻¹) - U) = 0 := by
      have hu' : Matrix.det (u • (Matrix.scalar (Fin n) (u⁻¹) - U)) = 0 := by
        simpa [hfactor] using hu
      rw [Matrix.det_smul, mul_eq_zero] at hu'
      exact hu'.resolve_left (pow_ne_zero _ hu0)
    have hspectrum : u⁻¹ ∈ spectrum ℂ U := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly]
      simpa using hsdet
    have hnorm_inv : ‖u⁻¹‖ = 1 := spectrum.norm_eq_one_of_unitary hU hspectrum
    have hnorm : ‖u‖ = 1 := by
      have hnorm_ne : ‖u‖ ≠ 0 := by simpa using hu0
      have hnorm_inv_eq : ‖u‖⁻¹ = 1 := by simpa [norm_inv] using hnorm_inv
      have hmul : ‖u‖ * ‖u‖⁻¹ = ‖u‖ * 1 := by rw [hnorm_inv_eq]
      have hnorm' : 1 = ‖u‖ := by simpa [hnorm_ne] using hmul
      exact hnorm'.symm
    simpa [Complex.abs] using hnorm

private theorem re_eq_half_of_det_cpow_eq_zero {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.IsUnitary) :
    ∀ {L : ℝ}, 1 < L → ∀ {s : ℂ},
      Matrix.det (1 - ((L : ℂ) ^ (2 * s - 1)) • U) = 0 → s.re = 1 / 2 := by
  intro L hL s hs
  have habs : Complex.abs ((L : ℂ) ^ (2 * s - 1)) = 1 :=
    abs_eq_one_of_det_one_sub_smul_eq_zero U hU _ hs
  have hpow : L ^ ((2 * s - 1).re) = 1 := by
    rw [← Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hL)]
    simpa [Complex.abs] using habs
  have hexp : (2 * s - 1).re = 0 := by
    apply (Real.strictMono_rpow_of_base_gt_one hL).injective
    simpa using hpow
  have hre : 2 * s.re - 1 = 0 := by
    simpa using hexp
  linarith

/-- Determinant zeros for a unitary matrix lie on the unit circle, and the resulting
    positive-real-power parameter is forced onto the critical line.
    prop:unitary-determinant-zero-unit-circle -/
theorem paper_unitary_determinant_zero_unit_circle {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.IsUnitary) :
    (∀ u : ℂ, Matrix.det (1 - u • U) = 0 → Complex.abs u = 1) ∧
      (∀ {L : ℝ}, 1 < L → ∀ {s : ℂ},
        Matrix.det (1 - ((L : ℂ) ^ (2 * s - 1)) • U) = 0 → s.re = 1 / 2) := by
  exact ⟨abs_eq_one_of_det_one_sub_smul_eq_zero U hU, re_eq_half_of_det_cpow_eq_zero U hU⟩

end Omega.Zeta
