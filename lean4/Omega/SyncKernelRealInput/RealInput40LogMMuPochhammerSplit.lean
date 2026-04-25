import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40ResidueConstant
import Omega.SyncKernelWeighted.FinitePartMuPochhammerSpectralClosedForm
import Omega.SyncKernelWeighted.MuPochhammerPhi1ExpMinusZ

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

noncomputable section

def logm_mu_pochhammer_split_pf_specialization : ℝ :=
  real_input_40_residue_constant_z_star

def logm_mu_pochhammer_split_correction : ℝ :=
  -logm_mu_pochhammer_split_pf_specialization +
    3 * logm_mu_pochhammer_split_pf_specialization ^ (2 : ℕ)

def logm_mu_pochhammer_split_pf_specialization_complex : ℂ :=
  (logm_mu_pochhammer_split_pf_specialization : ℂ)

def logm_mu_pochhammer_split_statement : Prop :=
  logm_mu_pochhammer_split_pf_specialization = (Real.goldenRatio⁻¹ : ℝ) ^ (2 : ℕ) ∧
    (∀ (spectrum : Finset ℂ) (mult : ℂ → ℕ) (mobius : ℕ → ℂ) (N : ℕ),
      mu_pochhammer_decomposition_mobius_log spectrum mult mobius
          logm_mu_pochhammer_split_pf_specialization_complex N =
        -(Finset.sum spectrum fun eig =>
          (mult eig : ℂ) * mu_pochhammer_decomposition_pochhammer_log eig mobius
            logm_mu_pochhammer_split_pf_specialization_complex N)) ∧
    (mu_pochhammer_phi1_exp_minus_z_log logm_mu_pochhammer_split_pf_specialization_complex =
      -logm_mu_pochhammer_split_pf_specialization_complex) ∧
    (((-2 : ℂ) *
        mu_pochhammer_phi1_exp_minus_z_log logm_mu_pochhammer_split_pf_specialization_complex +
        (-3 : ℂ) *
          (logm_mu_pochhammer_split_pf_specialization_complex -
            logm_mu_pochhammer_split_pf_specialization_complex ^ (2 : ℕ))) =
      (-logm_mu_pochhammer_split_pf_specialization_complex +
        3 * logm_mu_pochhammer_split_pf_specialization_complex ^ (2 : ℕ))) ∧
    logm_mu_pochhammer_split_correction = 9 - 4 * Real.sqrt 5

theorem paper_logm_mu_pochhammer_split : logm_mu_pochhammer_split_statement := by
  rcases paper_finite_part_mu_pochhammer_spectral_closed_form with ⟨hdecomp, _⟩
  rcases paper_mu_pochhammer_phi1_exp_minus_z with ⟨_, hphi1⟩
  have hzstar :
      logm_mu_pochhammer_split_pf_specialization = (Real.goldenRatio⁻¹ : ℝ) ^ (2 : ℕ) := by
    unfold logm_mu_pochhammer_split_pf_specialization real_input_40_residue_constant_z_star
      real_input_40_residue_constant_lambda
    rw [inv_pow]
  have hphi1_eval :
      mu_pochhammer_phi1_exp_minus_z_log logm_mu_pochhammer_split_pf_specialization_complex =
        -logm_mu_pochhammer_split_pf_specialization_complex := by
    exact (hphi1 logm_mu_pochhammer_split_pf_specialization_complex).1
  have hcollapsed :
      (-2 : ℂ) * mu_pochhammer_phi1_exp_minus_z_log
          logm_mu_pochhammer_split_pf_specialization_complex +
        (-3 : ℂ) *
          (logm_mu_pochhammer_split_pf_specialization_complex -
            logm_mu_pochhammer_split_pf_specialization_complex ^ (2 : ℕ)) =
      (-logm_mu_pochhammer_split_pf_specialization_complex +
        3 * logm_mu_pochhammer_split_pf_specialization_complex ^ (2 : ℕ)) := by
    rw [hphi1_eval]
    ring
  have hcorr : logm_mu_pochhammer_split_correction = 9 - 4 * Real.sqrt 5 := by
    have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ (2 : ℕ) = 5 := by
      norm_num
    have hsqrt5_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by
      positivity
    unfold logm_mu_pochhammer_split_correction logm_mu_pochhammer_split_pf_specialization
    rw [real_input_40_residue_constant_z_star_eq_two_sub_phi, Real.goldenRatio]
    ring_nf
    rw [hsqrt5_sq]
    nlinarith [hsqrt5_sq, hsqrt5_nonneg]
  refine ⟨hzstar, ?_, hphi1_eval, hcollapsed, hcorr⟩
  intro spectrum mult mobius N
  exact hdecomp spectrum mult mobius logm_mu_pochhammer_split_pf_specialization_complex N

end

end Omega.SyncKernelRealInput
