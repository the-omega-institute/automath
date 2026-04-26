import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

lemma xi_single_pole_contour_readout_error_audit_constant_ne_zero :
    (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  refine mul_ne_zero ?_ Complex.I_ne_zero
  exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)

lemma xi_single_pole_contour_readout_error_audit_constant_norm :
    ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  calc
    ‖(2 * Real.pi * Complex.I : ℂ)‖ = ‖((2 * Real.pi : ℂ))‖ * ‖(Complex.I : ℂ)‖ := by
      rw [norm_mul]
    _ = 2 * Real.pi := by
      have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi]

/-- Paper label: `thm:xi-single-pole-contour-readout-error-audit`. The contour data are encoded by
the two integrals `J₀,J₁`; exact residue and pole readout follow from algebraic cancellation, and
the audited error bounds come from the supplied contour sup-norm estimates together with the
standard quotient perturbation inequality. -/
theorem paper_xi_single_pole_contour_readout_error_audit
    (u0 residue J0 J1 J0Approx J1Approx : ℂ) (R eta contourSup : ℝ)
    (hR : 0 ≤ R) (heta : 0 ≤ eta) (hSup : 0 ≤ contourSup) (hResidue : residue ≠ 0)
    (hJ0 : J0 = (2 * Real.pi * Complex.I : ℂ) * residue)
    (hJ1 : J1 = (2 * Real.pi * Complex.I : ℂ) * u0 * residue)
    (hErr0 : ‖J0 - J0Approx‖ ≤ 2 * Real.pi * R * eta)
    (hErr1 : ‖J1 - J1Approx‖ ≤ 2 * Real.pi * R ^ 2 * eta)
    (hApprox : ‖J1Approx‖ ≤ 2 * Real.pi * R ^ 2 * contourSup)
    (hNondeg : 2 * Real.pi * R * eta < ‖J0Approx‖) :
    residue = ((1 / (2 * Real.pi * Complex.I : ℂ)) * J0) ∧
      u0 = J1 / J0 ∧
      ‖residue - ((1 / (2 * Real.pi * Complex.I : ℂ)) * J0Approx)‖ ≤ R * eta ∧
      ‖u0 - J1Approx / J0Approx‖ ≤
        (2 * Real.pi * R ^ 2 * eta) / (‖J0Approx‖ - 2 * Real.pi * R * eta) +
          ((2 * Real.pi * R ^ 2 * contourSup) * (2 * Real.pi * R * eta)) /
            ((‖J0Approx‖ - 2 * Real.pi * R * eta) * ‖J0Approx‖) := by
  let c : ℂ := (2 * Real.pi * Complex.I : ℂ)
  let delta0 : ℝ := 2 * Real.pi * R * eta
  let delta1 : ℝ := 2 * Real.pi * R ^ 2 * eta
  let B : ℝ := ‖J0Approx‖ - delta0
  have hc_ne : c ≠ 0 := xi_single_pole_contour_readout_error_audit_constant_ne_zero
  have hc_norm : ‖c‖ = 2 * Real.pi := xi_single_pole_contour_readout_error_audit_constant_norm
  have hJ0c : J0 = c * residue := by simpa [c] using hJ0
  have hJ1c : J1 = c * u0 * residue := by simpa [c] using hJ1
  have hErr0_bound : ‖J0 - J0Approx‖ ≤ delta0 := by simpa [delta0] using hErr0
  have hErr1_bound : ‖J1 - J1Approx‖ ≤ delta1 := by simpa [delta1] using hErr1
  have hApprox_bound : ‖J1Approx‖ ≤ 2 * Real.pi * R ^ 2 * contourSup := by
    simpa [delta1] using hApprox
  have hdelta0_nonneg : 0 ≤ delta0 := by
    dsimp [delta0]
    positivity
  have hB_pos : 0 < B := by
    simpa [B, delta0] using hNondeg
  have hJ0Approx_norm_pos : 0 < ‖J0Approx‖ := lt_of_le_of_lt hdelta0_nonneg hNondeg
  have hJ0Approx_ne : J0Approx ≠ 0 := by
    simpa using hJ0Approx_norm_pos.ne'
  have hJ0_ne : J0 ≠ 0 := by
    rw [hJ0c]
    exact mul_ne_zero hc_ne hResidue
  have hResidue_readout : residue = (1 / c) * J0 := by
    calc
      residue = (1 / c) * (c * residue) := by
        field_simp [hc_ne]
      _ = (1 / c) * J0 := by rw [← hJ0c]
  have hPole_readout : u0 = J1 / J0 := by
    rw [hJ1c, hJ0c]
    field_simp [hc_ne, hResidue]
  have hResidue_diff :
      residue - (1 / c) * J0Approx = (1 / c) * (J0 - J0Approx) := by
    rw [hResidue_readout]
    ring
  have hInvC_norm : ‖(1 / c : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [one_div, norm_inv, hc_norm]
  have hResidue_err :
      ‖residue - (1 / c) * J0Approx‖ ≤ R * eta := by
    calc
      ‖residue - (1 / c) * J0Approx‖ = ‖(1 / c) * (J0 - J0Approx)‖ := by
        rw [hResidue_diff]
      _ = ‖(1 / c : ℂ)‖ * ‖J0 - J0Approx‖ := by rw [norm_mul]
      _ ≤ ‖(1 / c : ℂ)‖ * delta0 := by
        exact mul_le_mul_of_nonneg_left hErr0_bound (norm_nonneg _)
      _ = R * eta := by
        rw [hInvC_norm]
        change (2 * Real.pi)⁻¹ * (2 * Real.pi * R * eta) = R * eta
        field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]
  have hJ0Approx_le :
      ‖J0Approx‖ ≤ ‖J0‖ + ‖J0 - J0Approx‖ := by
    calc
      ‖J0Approx‖ = ‖J0 + (J0Approx - J0)‖ := by congr 1; ring
      _ ≤ ‖J0‖ + ‖J0Approx - J0‖ := norm_add_le _ _
      _ = ‖J0‖ + ‖J0 - J0Approx‖ := by rw [norm_sub_rev]
  have hB_le_J0 : B ≤ ‖J0‖ := by
    dsimp [B, delta0]
    linarith
  have hQuotient_decomp :
      J1 / J0 - J1Approx / J0Approx =
        (J1 - J1Approx) / J0 + J1Approx * (J0Approx - J0) / (J0 * J0Approx) := by
    field_simp [hJ0_ne, hJ0Approx_ne]
    ring
  have hTerm1 :
      ‖(J1 - J1Approx) / J0‖ ≤ delta1 / B := by
    rw [norm_div]
    calc
      ‖J1 - J1Approx‖ / ‖J0‖ ≤ ‖J1 - J1Approx‖ / B := by
        exact div_le_div_of_nonneg_left (norm_nonneg _) hB_pos hB_le_J0
      _ ≤ delta1 / B := by
        refine div_le_div_of_nonneg_right ?_ hB_pos.le
        exact hErr1_bound
  have hDen2_pos : 0 < B * ‖J0Approx‖ := mul_pos hB_pos hJ0Approx_norm_pos
  have hDen2_le : B * ‖J0Approx‖ ≤ ‖J0‖ * ‖J0Approx‖ := by
    exact mul_le_mul_of_nonneg_right hB_le_J0 (norm_nonneg _)
  have hNum2 :
      ‖J1Approx‖ * ‖J0Approx - J0‖ ≤ (2 * Real.pi * R ^ 2 * contourSup) * delta0 := by
    have hErr0_rev : ‖J0Approx - J0‖ ≤ delta0 := by
      simpa [norm_sub_rev] using hErr0_bound
    exact mul_le_mul hApprox_bound hErr0_rev (norm_nonneg _) (by positivity)
  have hTerm2 :
      ‖J1Approx * (J0Approx - J0) / (J0 * J0Approx)‖ ≤
        ((2 * Real.pi * R ^ 2 * contourSup) * delta0) / (B * ‖J0Approx‖) := by
    rw [norm_div, norm_mul, norm_mul]
    calc
      (‖J1Approx‖ * ‖J0Approx - J0‖) / (‖J0‖ * ‖J0Approx‖) ≤
          (‖J1Approx‖ * ‖J0Approx - J0‖) / (B * ‖J0Approx‖) := by
            exact div_le_div_of_nonneg_left (by positivity) hDen2_pos hDen2_le
      _ ≤ ((2 * Real.pi * R ^ 2 * contourSup) * delta0) / (B * ‖J0Approx‖) := by
        exact div_le_div_of_nonneg_right hNum2 hDen2_pos.le
  have hPole_err :
      ‖u0 - J1Approx / J0Approx‖ ≤
        delta1 / B + ((2 * Real.pi * R ^ 2 * contourSup) * delta0) / (B * ‖J0Approx‖) := by
    calc
      ‖u0 - J1Approx / J0Approx‖ = ‖J1 / J0 - J1Approx / J0Approx‖ := by
        rw [hPole_readout]
      _ = ‖(J1 - J1Approx) / J0 + J1Approx * (J0Approx - J0) / (J0 * J0Approx)‖ := by
        rw [hQuotient_decomp]
      _ ≤ ‖(J1 - J1Approx) / J0‖ + ‖J1Approx * (J0Approx - J0) / (J0 * J0Approx)‖ :=
        norm_add_le _ _
      _ ≤ delta1 / B + ((2 * Real.pi * R ^ 2 * contourSup) * delta0) / (B * ‖J0Approx‖) := by
        gcongr
  refine ⟨by simpa [c] using hResidue_readout, hPole_readout, ?_, ?_⟩
  · simpa [c] using hResidue_err
  · simpa [delta0, delta1, B] using hPole_err

end

end Omega.Zeta
