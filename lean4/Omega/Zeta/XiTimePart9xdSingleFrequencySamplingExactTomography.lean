import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite Prony package for the single-frequency sampling theorem.  The data carry the
sample window, exact Prony reconstruction of decay nodes and coefficients, and the deterministic
post-processing maps that recover each atom coordinate. -/
structure xi_time_part9xd_single_frequency_sampling_exact_tomography_data where
  xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa : ℕ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_samples :
    Fin (2 * xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa) → ℂ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma :
    Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_delta :
    Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_mass :
    Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_lambda :
    Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℂ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff :
    Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℂ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_phase : ℝ → ℂ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius : ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_distinct_decay :
    Function.Injective xi_time_part9xd_single_frequency_sampling_exact_tomography_delta
  xi_time_part9xd_single_frequency_sampling_exact_tomography_mass_pos :
    ∀ j, 0 < xi_time_part9xd_single_frequency_sampling_exact_tomography_mass j
  xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff_ne_zero :
    ∀ j, xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j ≠ 0
  xi_time_part9xd_single_frequency_sampling_exact_tomography_prony :
    (Fin (2 * xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa) → ℂ) →
      Fin xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℂ × ℂ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_prony_exact :
    xi_time_part9xd_single_frequency_sampling_exact_tomography_prony
        xi_time_part9xd_single_frequency_sampling_exact_tomography_samples =
      fun j =>
        (xi_time_part9xd_single_frequency_sampling_exact_tomography_lambda j,
          xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j)
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_delta : ℂ → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_delta_exact :
    ∀ j,
      xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_delta
          (xi_time_part9xd_single_frequency_sampling_exact_tomography_lambda j) =
        xi_time_part9xd_single_frequency_sampling_exact_tomography_delta j
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_mass : ℂ → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_mass_exact :
    ∀ j,
      xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_mass
          (xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j) =
        xi_time_part9xd_single_frequency_sampling_exact_tomography_mass j
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma : ℂ → ℝ
  xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma_in_window :
    ∀ j,
      -xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius ≤
          xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma j ∧
        xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma j ≤
          xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius
  xi_time_part9xd_single_frequency_sampling_exact_tomography_recovered_gamma_in_window :
    ∀ j,
      -xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius ≤
          xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma
            (xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j) ∧
        xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma
            (xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j) ≤
          xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius
  xi_time_part9xd_single_frequency_sampling_exact_tomography_phase_match :
    ∀ j,
      xi_time_part9xd_single_frequency_sampling_exact_tomography_phase
          (xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma
            (xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j)) =
        xi_time_part9xd_single_frequency_sampling_exact_tomography_phase
          (xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma j)
  xi_time_part9xd_single_frequency_sampling_exact_tomography_phase_injective_on_window :
    ∀ {γ γ' : ℝ},
      -xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius ≤ γ →
        γ ≤ xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius →
        -xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius ≤ γ' →
        γ' ≤ xi_time_part9xd_single_frequency_sampling_exact_tomography_window_radius →
        xi_time_part9xd_single_frequency_sampling_exact_tomography_phase γ =
          xi_time_part9xd_single_frequency_sampling_exact_tomography_phase γ' →
        γ = γ'

namespace xi_time_part9xd_single_frequency_sampling_exact_tomography_data

/-- The original ordered atom list. -/
def xi_time_part9xd_single_frequency_sampling_exact_tomography_atoms
    (D : xi_time_part9xd_single_frequency_sampling_exact_tomography_data) :
    Fin D.xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℝ × ℝ × ℝ :=
  fun j =>
    (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma j,
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_delta j,
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_mass j)

/-- Atoms reconstructed by first applying the exact Prony package to the `2κ` samples and then
decoding phase, decay, and positive mass. -/
def xi_time_part9xd_single_frequency_sampling_exact_tomography_reconstructedAtoms
    (D : xi_time_part9xd_single_frequency_sampling_exact_tomography_data) :
    Fin D.xi_time_part9xd_single_frequency_sampling_exact_tomography_kappa → ℝ × ℝ × ℝ :=
  fun j =>
    let z := D.xi_time_part9xd_single_frequency_sampling_exact_tomography_prony
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_samples j
    (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma z.2,
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_delta z.1,
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_mass z.2)

/-- The finite single-frequency sample window determines all atom coordinates. -/
def xi_time_part9xd_single_frequency_sampling_exact_tomography_samplesDetermineAtoms
    (D : xi_time_part9xd_single_frequency_sampling_exact_tomography_data) : Prop :=
  D.xi_time_part9xd_single_frequency_sampling_exact_tomography_reconstructedAtoms =
    D.xi_time_part9xd_single_frequency_sampling_exact_tomography_atoms

end xi_time_part9xd_single_frequency_sampling_exact_tomography_data

open xi_time_part9xd_single_frequency_sampling_exact_tomography_data

/-- Paper label: `thm:xi-time-part9xd-single-frequency-sampling-exact-tomography`. -/
theorem paper_xi_time_part9xd_single_frequency_sampling_exact_tomography
    (D : xi_time_part9xd_single_frequency_sampling_exact_tomography_data) :
    D.xi_time_part9xd_single_frequency_sampling_exact_tomography_samplesDetermineAtoms := by
  funext j
  have hprony := congrFun
    D.xi_time_part9xd_single_frequency_sampling_exact_tomography_prony_exact j
  have hgamma :
      D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_gamma
          (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_coeff j) =
        D.xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma j := by
    exact D.xi_time_part9xd_single_frequency_sampling_exact_tomography_phase_injective_on_window
      (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recovered_gamma_in_window j).1
      (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recovered_gamma_in_window j).2
      (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma_in_window j).1
      (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_gamma_in_window j).2
      (D.xi_time_part9xd_single_frequency_sampling_exact_tomography_phase_match j)
  simp [
    xi_time_part9xd_single_frequency_sampling_exact_tomography_reconstructedAtoms,
    xi_time_part9xd_single_frequency_sampling_exact_tomography_atoms,
    hprony,
    hgamma,
    D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_delta_exact j,
    D.xi_time_part9xd_single_frequency_sampling_exact_tomography_recover_mass_exact j]

end Omega.Zeta
