import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

open Matrix

noncomputable section

/-- Off-diagonal derivative contribution from the critical-point equations. -/
def xi_basepoint_scan_critical_jacobian_calogero_symmetric_offdiag_deriv
    (xi xj : ℝ) : ℝ :=
  ((xi - xj) ^ 2)⁻¹

/-- Diagonal pole contribution coming from differentiating `-Re (1 / (x_i - p_k))`. -/
def xi_basepoint_scan_critical_jacobian_calogero_symmetric_pole_diag_term
    (xi : ℝ) (pk : ℂ) : ℝ :=
  Complex.re (((((xi : ℂ) - pk) ^ 2)⁻¹))

/-- The diagonal entry is the sum of all diagonal derivative contributions. -/
def xi_basepoint_scan_critical_jacobian_calogero_symmetric_diag_entry
    {κ : ℕ} (x : Fin κ → ℝ) (p : Fin κ → ℂ) (i : Fin κ) : ℝ :=
  -((Finset.univ.erase i).sum fun l =>
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_offdiag_deriv (x i) (x l)) +
    Finset.univ.sum fun k =>
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_pole_diag_term (x i) (p k)

/-- The Calogero-type Jacobian obtained by differentiating the critical equations entrywise. -/
def xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian
    {κ : ℕ} (x : Fin κ → ℝ) (p : Fin κ → ℂ) : Matrix (Fin κ) (Fin κ) ℝ :=
  fun i j =>
    if i = j then
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_diag_entry x p i
    else
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_offdiag_deriv (x i) (x j)

/-- Paper label: `thm:xi-basepoint-scan-critical-jacobian-calogero-symmetric`. Differentiating
the off-diagonal and diagonal pieces of the critical equations produces the explicit Calogero
matrix formula; the off-diagonal kernel is symmetric, and the associated linear operator is a unit
exactly when the only zero-mode is the trivial one. -/
theorem paper_xi_basepoint_scan_critical_jacobian_calogero_symmetric
    (κ : ℕ) (x : Fin κ → ℝ) (p : Fin κ → ℂ) :
    (∀ i j, i ≠ j →
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian x p i j =
        ((x i - x j) ^ 2)⁻¹) ∧
    (∀ i,
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian x p i i =
        -((Finset.univ.erase i).sum fun l => ((x i - x l) ^ 2)⁻¹) +
          Finset.univ.sum fun k =>
            xi_basepoint_scan_critical_jacobian_calogero_symmetric_pole_diag_term (x i) (p k)) ∧
    (xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian x p).IsSymm ∧
    (IsUnit (xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian x p).toLin' ↔
      ∀ v,
        xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian x p *ᵥ v = 0 →
          v = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian, hij,
      xi_basepoint_scan_critical_jacobian_calogero_symmetric_offdiag_deriv]
  · intro i
    simp only [xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian]
    rfl
  · ext i j
    by_cases h : i = j
    · subst h
      simp [xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian]
    · have hji : j ≠ i := fun h' => h h'.symm
      simp [Matrix.transpose_apply, xi_basepoint_scan_critical_jacobian_calogero_symmetric_jacobian,
        h, hji]
      have hsq : (x i - x j) ^ 2 = (x j - x i) ^ 2 := by ring
      simpa [xi_basepoint_scan_critical_jacobian_calogero_symmetric_offdiag_deriv] using
        congrArg Inv.inv hsq.symm
  · rw [LinearMap.isUnit_iff_ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]

end

end Omega.Zeta
