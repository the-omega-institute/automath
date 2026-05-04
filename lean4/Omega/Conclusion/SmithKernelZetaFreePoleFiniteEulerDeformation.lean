import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite torsion support of the sample Smith profile. -/
def conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support : Finset ℕ :=
  ({2, 3, 5} : Finset ℕ)

/-- The local Euler deformation factor: free primes contribute `1`. -/
def conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor
    (p : ℕ) : ℕ :=
  if p ∈ conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support then p else 1

/-- Paper label: `thm:conclusion-smith-kernel-zeta-free-pole-finite-euler-deformation`. -/
def conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_statement : Prop :=
  (∀ p : ℕ, p ∉ conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support →
    conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor p = 1) ∧
    (Finset.prod conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support
      conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor = 30) ∧
      (∀ p : ℕ,
        p ∈ conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support →
        1 <
          conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor p)

theorem paper_conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation :
    conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_statement := by
  constructor
  · intro p hp
    simp [conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor, hp]
  constructor
  · native_decide
  · intro p hp
    rw [conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_local_factor]
    simp only [if_pos hp]
    simp only [conclusion_smith_kernel_zeta_free_pole_finite_euler_deformation_support,
      Finset.mem_insert, Finset.mem_singleton] at hp
    omega

end Omega.Conclusion
