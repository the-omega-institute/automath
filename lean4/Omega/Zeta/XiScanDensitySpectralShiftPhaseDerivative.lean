import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Tactic
import Omega.Zeta.XiDefectEntropyHyperbolicAreaLaw4pi

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite defect data for the phase-derivative scan profile. -/
structure xi_scan_density_spectral_shift_phase_derivative_data where
  κ : ℕ
  gamma : Fin κ → ℝ
  delta : Fin κ → ℝ
  multiplicity : Fin κ → ℕ
  delta_pos : ∀ j : Fin κ, 0 < delta j

/-- The shifted half-width `1 + δ_j` of the `j`-th defect packet. -/
def xi_scan_density_spectral_shift_phase_derivative_scale
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (j : Fin D.κ) : ℝ :=
  1 + D.delta j

/-- The single-factor logarithmic derivative on the real boundary. -/
def xi_scan_density_spectral_shift_phase_derivative_single_factor_log_derivative
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (j : Fin D.κ) (x : ℝ) : ℂ :=
  (1 : ℂ) /
      (((x - D.gamma j : ℝ) : ℂ) -
        Complex.I * (xi_scan_density_spectral_shift_phase_derivative_scale D j : ℂ)) -
    (1 : ℂ) /
      (((x - D.gamma j : ℝ) : ℂ) +
        Complex.I * (xi_scan_density_spectral_shift_phase_derivative_scale D j : ℂ))

/-- The phase derivative is the imaginary part of the logarithmic derivative. -/
def xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (j : Fin D.κ) (x : ℝ) : ℝ :=
  Complex.im
    (xi_scan_density_spectral_shift_phase_derivative_single_factor_log_derivative D j x)

/-- The total phase derivative after summing over the finite defect family. -/
def xi_scan_density_spectral_shift_phase_derivative_total_phase_derivative
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (x : ℝ) : ℝ :=
  ∑ j : Fin D.κ,
    (D.multiplicity j : ℝ) *
      xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative D j x

/-- The concrete scan profile `H(x)` from the paper. -/
def xi_scan_density_spectral_shift_phase_derivative_scan_profile
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (x : ℝ) : ℝ :=
  ∑ j : Fin D.κ,
    (D.multiplicity j : ℝ) * (4 * D.delta j) /
      (((x - D.gamma j) ^ 2) +
        (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)

/-- The total mass written as the explicit finite sum of Cauchy-kernel integrals. -/
def xi_scan_density_spectral_shift_phase_derivative_total_mass
    (D : xi_scan_density_spectral_shift_phase_derivative_data) : ℝ :=
  ∑ j : Fin D.κ,
    ∫ x : ℝ,
      (D.multiplicity j : ℝ) * (4 * D.delta j) /
        (((x - D.gamma j) ^ 2) +
          (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)

private lemma xi_scan_density_spectral_shift_phase_derivative_scale_pos
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (j : Fin D.κ) :
    0 < xi_scan_density_spectral_shift_phase_derivative_scale D j := by
  unfold xi_scan_density_spectral_shift_phase_derivative_scale
  linarith [D.delta_pos j]

private lemma xi_scan_density_spectral_shift_phase_derivative_inv_sub_im
    (u a : ℝ) :
    Complex.im
        ((1 : ℂ) / ((u : ℂ) - Complex.I * (a : ℂ)) -
          (1 : ℂ) / ((u : ℂ) + Complex.I * (a : ℂ))) =
      2 * a / (u ^ 2 + a ^ 2) := by
  have hfirst :
      Complex.im ((1 : ℂ) / ((u : ℂ) - Complex.I * (a : ℂ))) = a / (u ^ 2 + a ^ 2) := by
    have hnorm :
        Complex.normSq ((u : ℂ) - Complex.I * (a : ℂ)) = u ^ 2 + a ^ 2 := by
      simp [Complex.normSq, sq]
    rw [Complex.div_im]
    simp [hnorm]
    ring_nf
  have hsecond :
      Complex.im ((1 : ℂ) / ((u : ℂ) + Complex.I * (a : ℂ))) = -a / (u ^ 2 + a ^ 2) := by
    have hnorm :
        Complex.normSq ((u : ℂ) + Complex.I * (a : ℂ)) = u ^ 2 + a ^ 2 := by
      simp [Complex.normSq, sq]
    rw [Complex.div_im]
    simp [hnorm]
    ring_nf
  rw [Complex.sub_im, hfirst, hsecond]
  ring

private lemma xi_scan_density_spectral_shift_phase_derivative_single_factor_formula
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (j : Fin D.κ) (x : ℝ) :
    xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative D j x =
      2 * xi_scan_density_spectral_shift_phase_derivative_scale D j /
        (((x - D.gamma j) ^ 2) +
          (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2) := by
  unfold xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative
    xi_scan_density_spectral_shift_phase_derivative_single_factor_log_derivative
  simpa using
    xi_scan_density_spectral_shift_phase_derivative_inv_sub_im
      (x - D.gamma j) (xi_scan_density_spectral_shift_phase_derivative_scale D j)

private lemma xi_scan_density_spectral_shift_phase_derivative_total_phase_formula
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (x : ℝ) :
    xi_scan_density_spectral_shift_phase_derivative_total_phase_derivative D x =
      2 *
        ∑ j : Fin D.κ,
          (D.multiplicity j : ℝ) *
            (xi_scan_density_spectral_shift_phase_derivative_scale D j /
              (((x - D.gamma j) ^ 2) +
                (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)) := by
  calc
    xi_scan_density_spectral_shift_phase_derivative_total_phase_derivative D x =
        ∑ j : Fin D.κ,
          (D.multiplicity j : ℝ) *
            (2 * xi_scan_density_spectral_shift_phase_derivative_scale D j /
              (((x - D.gamma j) ^ 2) +
                (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)) := by
          unfold xi_scan_density_spectral_shift_phase_derivative_total_phase_derivative
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [xi_scan_density_spectral_shift_phase_derivative_single_factor_formula D j x]
    _ =
        ∑ j : Fin D.κ,
          2 *
            ((D.multiplicity j : ℝ) *
              (xi_scan_density_spectral_shift_phase_derivative_scale D j /
                (((x - D.gamma j) ^ 2) +
                  (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ =
        2 *
          ∑ j : Fin D.κ,
            (D.multiplicity j : ℝ) *
              (xi_scan_density_spectral_shift_phase_derivative_scale D j /
                (((x - D.gamma j) ^ 2) +
                  (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)) := by
          symm
          rw [Finset.mul_sum]

private lemma xi_scan_density_spectral_shift_phase_derivative_scan_profile_formula
    (D : xi_scan_density_spectral_shift_phase_derivative_data) (x : ℝ) :
    xi_scan_density_spectral_shift_phase_derivative_scan_profile D x =
      ∑ j : Fin D.κ,
        (D.multiplicity j : ℝ) *
          (2 * D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) *
            xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative D j x := by
  unfold xi_scan_density_spectral_shift_phase_derivative_scan_profile
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [xi_scan_density_spectral_shift_phase_derivative_single_factor_formula D j x]
  have hscale_ne :
      xi_scan_density_spectral_shift_phase_derivative_scale D j ≠ 0 := by
    exact ne_of_gt (xi_scan_density_spectral_shift_phase_derivative_scale_pos D j)
  field_simp [hscale_ne]
  ring

private lemma xi_scan_density_spectral_shift_phase_derivative_total_mass_formula
    (D : xi_scan_density_spectral_shift_phase_derivative_data) :
    xi_scan_density_spectral_shift_phase_derivative_total_mass D =
      4 * Real.pi *
        ∑ j : Fin D.κ,
          (D.multiplicity j : ℝ) *
            (D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) := by
  have hmass :=
    paper_xi_defect_entropy_hyperbolic_area_law_4pi D.gamma D.delta D.multiplicity D.delta_pos
  have hrewrite :
      ∑ j : Fin D.κ,
          (D.multiplicity j : ℝ) *
            (D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) =
        (1 / (4 * Real.pi)) *
          ∑ j : Fin D.κ,
            ∫ x : ℝ,
              (D.multiplicity j : ℝ) * (4 * D.delta j) /
                (((x - D.gamma j) ^ 2) +
                  (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2) := by
    simpa [xi_scan_density_spectral_shift_phase_derivative_scale] using hmass
  calc
    xi_scan_density_spectral_shift_phase_derivative_total_mass D =
        4 * Real.pi *
          ((1 / (4 * Real.pi)) *
            ∑ j : Fin D.κ,
              ∫ x : ℝ,
                (D.multiplicity j : ℝ) * (4 * D.delta j) /
                  (((x - D.gamma j) ^ 2) +
                    (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2)) := by
          unfold xi_scan_density_spectral_shift_phase_derivative_total_mass
          have hfour_pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
          symm
          field_simp [hfour_pi_ne]
    _ =
        4 * Real.pi *
          ∑ j : Fin D.κ,
            (D.multiplicity j : ℝ) *
              (D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) := by
          rw [← hrewrite]

/-- Paper label: `prop:xi-scan-density-spectral-shift-phase-derivative`.
The single-factor logarithmic derivative is the explicit Cauchy kernel, summing over the finite
defect family produces the weighted spectral-shift density, and integrating the scan profile gives
the total mass identity. -/
theorem paper_xi_scan_density_spectral_shift_phase_derivative
    (D : xi_scan_density_spectral_shift_phase_derivative_data) :
    (∀ x : ℝ,
      xi_scan_density_spectral_shift_phase_derivative_total_phase_derivative D x =
        2 *
          ∑ j : Fin D.κ,
            (D.multiplicity j : ℝ) *
              (xi_scan_density_spectral_shift_phase_derivative_scale D j /
                (((x - D.gamma j) ^ 2) +
                  (xi_scan_density_spectral_shift_phase_derivative_scale D j) ^ 2))) ∧
      (∀ x : ℝ,
        xi_scan_density_spectral_shift_phase_derivative_scan_profile D x =
          ∑ j : Fin D.κ,
            (D.multiplicity j : ℝ) *
              (2 * D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) *
                xi_scan_density_spectral_shift_phase_derivative_single_factor_phase_derivative D j
                  x) ∧
      xi_scan_density_spectral_shift_phase_derivative_total_mass D =
        4 * Real.pi *
          ∑ j : Fin D.κ,
            (D.multiplicity j : ℝ) *
              (D.delta j / xi_scan_density_spectral_shift_phase_derivative_scale D j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact xi_scan_density_spectral_shift_phase_derivative_total_phase_formula D x
  · intro x
    exact xi_scan_density_spectral_shift_phase_derivative_scan_profile_formula D x
  · exact xi_scan_density_spectral_shift_phase_derivative_total_mass_formula D

end

end Omega.Zeta
