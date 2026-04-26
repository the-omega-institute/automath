import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40PrimedirichletBranchInherit
import Omega.SyncKernelRealInput.FiniteRh40

namespace Omega.SyncKernelWeighted

noncomputable section

open Omega.SyncKernelRealInput

/-- The odd critical-line branch point before the prime-Dirichlet rescaling. -/
def real_input_40_primedirichlet_branch_halfp_critical_point (m : ℕ) : ℂ :=
  ⟨(1 : ℝ) / 2,
    ((2 * (m : ℝ) + 1) * Real.pi) / Real.log finite_rh_40_lambda⟩

/-- The branch point obtained after dividing the critical-line point by an odd prime `p`. -/
def real_input_40_primedirichlet_branch_halfp_prime_point (p m : ℕ) : ℂ :=
  (p : ℂ)⁻¹ * real_input_40_primedirichlet_branch_halfp_critical_point m

/-- Concrete audited data used to invoke the finite-RH real-input-40 package. -/
def real_input_40_primedirichlet_branch_halfp_finite_rh_data : finite_rh_40_data where
  auditedSpectrum := finite_rh_40_audited_spectrum
  auditedSpectrum_eq := rfl

/-- The explicit half-line branch package: the inherited prime-Dirichlet branch theorem holds,
the finite-RH audit supplies the critical branch, and division by an odd prime sends the real
coordinate from `1 / 2` to `1 / (2 * p)` while preserving the displayed height formula. -/
def real_input_40_primedirichlet_branch_halfp_statement : Prop :=
  primedirichlet_branch_inherit_statement ∧
    finite_rh_40_statement real_input_40_primedirichlet_branch_halfp_finite_rh_data ∧
      ∀ p m : ℕ, Nat.Prime p → Odd p →
        (real_input_40_primedirichlet_branch_halfp_prime_point p m).re =
            (1 : ℝ) / (2 * (p : ℝ)) ∧
          (real_input_40_primedirichlet_branch_halfp_prime_point p m).im =
            ((2 * (m : ℝ) + 1) * Real.pi) /
              ((p : ℝ) * Real.log finite_rh_40_lambda)

/-- Paper label: `cor:real-input-40-primedirichlet-branch-halfp`. -/
theorem paper_real_input_40_primedirichlet_branch_halfp :
    real_input_40_primedirichlet_branch_halfp_statement := by
  refine ⟨paper_primedirichlet_branch_inherit, ?_, ?_⟩
  · exact paper_finite_rh_40 real_input_40_primedirichlet_branch_halfp_finite_rh_data
  · intro p m hp _hodd
    have hp_ne_real : (p : ℝ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    constructor
    · simp [real_input_40_primedirichlet_branch_halfp_prime_point,
        real_input_40_primedirichlet_branch_halfp_critical_point, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
      field_simp [hp_ne_real]
    · simp [real_input_40_primedirichlet_branch_halfp_prime_point,
        real_input_40_primedirichlet_branch_halfp_critical_point, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
      field_simp [hp_ne_real]

end

end Omega.SyncKernelWeighted
