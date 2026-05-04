import Omega.Zeta.XiBasepointScanL2EnergyPdKernel

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The diagonal part of the finite L2-energy expansion gives a concrete lower bound, and the
energy is nonnegative. -/
def xi_basepoint_scan_l2_energy_diagonal_lower_bound_statement
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) : Prop :=
  16 * (∑ j : Fin D.κ,
    (D.delta j) ^ 2 * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j j) ≤
      xi_basepoint_scan_l2_energy_pd_kernel_energy D ∧
    0 ≤ xi_basepoint_scan_l2_energy_pd_kernel_energy D

/-- Paper label: `cor:xi-basepoint-scan-l2-energy-diagonal-lower-bound`. -/
theorem paper_xi_basepoint_scan_l2_energy_diagonal_lower_bound
    (D : xi_basepoint_scan_l2_energy_pd_kernel_data) :
    xi_basepoint_scan_l2_energy_diagonal_lower_bound_statement D := by
  classical
  rcases paper_xi_basepoint_scan_l2_energy_pd_kernel D with ⟨henergy, hpsd⟩
  have hdiag :
      (∑ j : Fin D.κ, ∑ k : Fin D.κ,
          D.delta j * D.delta k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k) =
        ∑ j : Fin D.κ,
          (D.delta j) ^ 2 * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j j := by
    simp [xi_basepoint_scan_l2_energy_pd_kernel_matrix]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have henergy_diag :
      xi_basepoint_scan_l2_energy_pd_kernel_energy D =
        16 * (∑ j : Fin D.κ,
          (D.delta j) ^ 2 * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j j) := by
    rw [henergy, hdiag]
  have hnonneg_sum :
      0 ≤ ∑ j : Fin D.κ, ∑ k : Fin D.κ,
        D.delta j * D.delta k * xi_basepoint_scan_l2_energy_pd_kernel_matrix D j k :=
    hpsd D.delta
  have hnonneg_energy : 0 ≤ xi_basepoint_scan_l2_energy_pd_kernel_energy D := by
    rw [henergy]
    exact mul_nonneg (by norm_num) hnonneg_sum
  exact ⟨by rw [henergy_diag], hnonneg_energy⟩

end

end Omega.Zeta
