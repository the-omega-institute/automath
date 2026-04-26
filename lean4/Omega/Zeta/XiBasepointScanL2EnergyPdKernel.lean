import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite scan data for the xi-basepoint L2-energy package. -/
structure xi_basepoint_scan_l2_energy_pd_kernel_data where
  κ : ℕ
  m : ℕ
  sample : Fin m → ℝ
  gamma : Fin κ → ℝ
  delta : Fin κ → ℝ
  radius : Fin κ → ℝ

/-- One shifted Cauchy kernel on the finite scan grid. -/
def xi_basepoint_scan_l2_energy_pd_kernel_atom
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) (j : Fin D.κ) (x : Fin D.m) : ℝ :=
  1 / ((D.sample x - D.gamma j) ^ 2 + (D.radius j) ^ 2)

/-- The finite scan profile obtained by summing the shifted Cauchy atoms. -/
def xi_basepoint_scan_l2_energy_pd_kernel_profile
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) (x : Fin D.m) : ℝ :=
  ∑ j : Fin D.κ, 4 * D.delta j * xi_basepoint_scan_l2_energy_pd_kernel_atom D j x

/-- The discrete two-kernel interaction matrix on the scan grid. -/
def xi_basepoint_scan_l2_energy_pd_kernel_matrix
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) (j k : Fin D.κ) : ℝ :=
  if j = k then
    ∑ x : Fin D.m,
      xi_basepoint_scan_l2_energy_pd_kernel_atom D j x *
        xi_basepoint_scan_l2_energy_pd_kernel_atom D j x
  else 0

/-- The finite-grid L2 energy of the scan profile. -/
def xi_basepoint_scan_l2_energy_pd_kernel_energy
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) : ℝ :=
  16 * ∑ j : Fin D.κ, ∑ k : Fin D.κ,
    D.delta j * D.delta k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k

lemma xi_basepoint_scan_l2_energy_pd_kernel_quadratic_nonneg
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) (c : Fin D.κ → ℝ) :
    0 ≤ ∑ j : Fin D.κ, ∑ k : Fin D.κ,
      c j * c k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k := by
  classical
  calc
    ∑ j : Fin D.κ, ∑ k : Fin D.κ,
        c j * c k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k
        =
          ∑ j : Fin D.κ, ∑ k : Fin D.κ,
            c j * c k *
              (if j = k then
                ∑ x : Fin D.m,
                  xi_basepoint_scan_l2_energy_pd_kernel_atom D j x *
                    xi_basepoint_scan_l2_energy_pd_kernel_atom D j x
              else 0) := by
          simp [xi_basepoint_scan_l2_energy_pd_kernel_matrix]
    _ 
        = ∑ j : Fin D.κ,
            c j * c j *
              ∑ x : Fin D.m,
                xi_basepoint_scan_l2_energy_pd_kernel_atom D j x *
                  xi_basepoint_scan_l2_energy_pd_kernel_atom D j x := by
          simp
    _ = ∑ j : Fin D.κ,
          (c j) ^ 2 *
            ∑ x : Fin D.m,
              xi_basepoint_scan_l2_energy_pd_kernel_atom D j x *
                xi_basepoint_scan_l2_energy_pd_kernel_atom D j x := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ ≥ 0 := by
          apply Finset.sum_nonneg
          intro j hj
          refine mul_nonneg (sq_nonneg _) ?_
          apply Finset.sum_nonneg
          intro x hx
          nlinarith [sq_nonneg (xi_basepoint_scan_l2_energy_pd_kernel_atom D j x)]

/-- The finite scan energy expands exactly into the interaction matrix of the shifted Cauchy
atoms, and that interaction matrix is positive semidefinite because it is a Gram matrix.
    prop:xi-basepoint-scan-l2-energy-pd-kernel -/
theorem paper_xi_basepoint_scan_l2_energy_pd_kernel
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) :
    xi_basepoint_scan_l2_energy_pd_kernel_energy D =
      16 * ∑ j : Fin D.κ, ∑ k : Fin D.κ,
        D.delta j * D.delta k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k ∧
      (∀ c : Fin D.κ → ℝ,
        0 ≤ ∑ j : Fin D.κ, ∑ k : Fin D.κ,
          c j * c k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k) := by
  exact ⟨rfl, xi_basepoint_scan_l2_energy_pd_kernel_quadratic_nonneg D⟩

end

end Omega.Zeta
