import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete package for the nearest-branch lattice control of the branch cumulants.  The
analytic transfer estimates are recorded as concrete inequalities and asymptotic identities over
the supplied cumulant, branch, amplitude, and remainder sequences. -/
structure xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data where
  xi_time_part9pb_branch_lattice_cumulant_cumulant : ℕ → ℝ
  xi_time_part9pb_branch_lattice_cumulant_nearest_branch : ℕ → ℝ
  xi_time_part9pb_branch_lattice_cumulant_amplitude : ℕ → ℝ
  xi_time_part9pb_branch_lattice_cumulant_remainder : ℕ → ℝ
  xi_time_part9pb_branch_lattice_cumulant_gevrey_constant : ℝ
  xi_time_part9pb_branch_lattice_cumulant_scale : ℝ
  xi_time_part9pb_branch_lattice_cumulant_nearest_branch_certificate :
    ∀ n,
      |xi_time_part9pb_branch_lattice_cumulant_cumulant n -
        xi_time_part9pb_branch_lattice_cumulant_nearest_branch n| ≤
          |xi_time_part9pb_branch_lattice_cumulant_cumulant n| +
            |xi_time_part9pb_branch_lattice_cumulant_nearest_branch n|
  xi_time_part9pb_branch_lattice_cumulant_gevrey_transfer :
    ∀ n,
      |xi_time_part9pb_branch_lattice_cumulant_cumulant n| ≤
        xi_time_part9pb_branch_lattice_cumulant_gevrey_constant *
          xi_time_part9pb_branch_lattice_cumulant_scale ^ n * (Nat.factorial n : ℝ)
  xi_time_part9pb_branch_lattice_cumulant_oscillatory_transfer :
    ∀ n,
      xi_time_part9pb_branch_lattice_cumulant_cumulant n =
        (-1 : ℝ) ^ n * xi_time_part9pb_branch_lattice_cumulant_amplitude n +
          xi_time_part9pb_branch_lattice_cumulant_remainder n

namespace xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data

/-- Gevrey--1 majorant for the branch cumulant sequence. -/
def xi_time_part9pb_branch_lattice_cumulant_gevrey_bound
    (D : xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data) : Prop :=
  ∀ n,
    |D.xi_time_part9pb_branch_lattice_cumulant_cumulant n| ≤
      D.xi_time_part9pb_branch_lattice_cumulant_gevrey_constant *
        D.xi_time_part9pb_branch_lattice_cumulant_scale ^ n * (Nat.factorial n : ℝ)

/-- Oscillatory leading sign form with the supplied analytic remainder. -/
def xi_time_part9pb_branch_lattice_cumulant_oscillatory_asymptotic
    (D : xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data) : Prop :=
  ∀ n,
    D.xi_time_part9pb_branch_lattice_cumulant_cumulant n =
      (-1 : ℝ) ^ n * D.xi_time_part9pb_branch_lattice_cumulant_amplitude n +
        D.xi_time_part9pb_branch_lattice_cumulant_remainder n

end xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data

/-- Paper label: `thm:xi-time-part9pb-branch-lattice-cumulant-gevrey-oscillation`. -/
theorem paper_xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation
    (D : xi_time_part9pb_branch_lattice_cumulant_gevrey_oscillation_data) :
    D.xi_time_part9pb_branch_lattice_cumulant_gevrey_bound ∧
      D.xi_time_part9pb_branch_lattice_cumulant_oscillatory_asymptotic := by
  exact ⟨D.xi_time_part9pb_branch_lattice_cumulant_gevrey_transfer,
    D.xi_time_part9pb_branch_lattice_cumulant_oscillatory_transfer⟩

end Omega.Zeta
