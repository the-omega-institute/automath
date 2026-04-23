import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete Cauchy-profile data for the `L¹`/`L²`/peak witness. The finite profile is a sum of
nonnegative translated Cauchy kernels; the chosen `peakIndex` records the atom whose diagonal
contribution dominates the diagonal `L²` lower bound. -/
structure xi_scan_profile_lp_peak_witness_data (κ : ℕ) where
  gamma : Fin κ → ℝ
  scale : Fin κ → ℝ
  weight : Fin κ → ℝ
  peakIndex : Fin κ
  scale_pos : ∀ j : Fin κ, 0 < scale j
  weight_nonneg : ∀ j : Fin κ, 0 ≤ weight j
  totalMass_pos : 0 < ∑ j : Fin κ, weight j
  peakIndex_max :
    ∀ j : Fin κ,
      weight j / (2 * Real.pi * scale j) ≤
        weight peakIndex / (2 * Real.pi * scale peakIndex)

/-- One nonnegative translated Cauchy kernel. -/
def xi_scan_profile_lp_peak_witness_kernel {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) (j : Fin κ) (x : ℝ) : ℝ :=
  D.scale j / (Real.pi * ((x - D.gamma j) ^ 2 + (D.scale j) ^ 2))

/-- The finite scan profile obtained by summing the weighted Cauchy kernels. -/
def xi_scan_profile_lp_peak_witness_profile {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) (x : ℝ) : ℝ :=
  ∑ j : Fin κ, D.weight j * xi_scan_profile_lp_peak_witness_kernel D j x

/-- The exact `L¹` mass predicted by the normalized Cauchy kernels. -/
def xi_scan_profile_lp_peak_witness_l1_identity {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) : ℝ :=
  ∑ j : Fin κ, D.weight j

/-- The diagonal-only `L²` lower bound obtained by discarding the nonnegative cross terms. -/
def xi_scan_profile_lp_peak_witness_l2_diagonal_lower {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) : ℝ :=
  ∑ j : Fin κ, D.weight j ^ 2 / (2 * Real.pi * D.scale j)

/-- The peak ratio singled out by the maximizing atom. -/
def xi_scan_profile_lp_peak_witness_peak_ratio {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) : ℝ :=
  D.weight D.peakIndex / (2 * Real.pi * D.scale D.peakIndex)

/-- Paper-facing `L¹`/`L²`/`L∞` witness package for the finite Cauchy profile. -/
def xi_scan_profile_lp_peak_witness_holds {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) : Prop :=
  (∀ x : ℝ, 0 ≤ xi_scan_profile_lp_peak_witness_profile D x) ∧
    0 < xi_scan_profile_lp_peak_witness_l1_identity D ∧
    0 ≤ xi_scan_profile_lp_peak_witness_l2_diagonal_lower D ∧
    xi_scan_profile_lp_peak_witness_l2_diagonal_lower D /
        xi_scan_profile_lp_peak_witness_l1_identity D ≤
      xi_scan_profile_lp_peak_witness_profile D (D.gamma D.peakIndex)

private theorem xi_scan_profile_lp_peak_witness_kernel_nonneg {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) (j : Fin κ) (x : ℝ) :
    0 ≤ xi_scan_profile_lp_peak_witness_kernel D j x := by
  unfold xi_scan_profile_lp_peak_witness_kernel
  have hden : 0 ≤ Real.pi * ((x - D.gamma j) ^ 2 + (D.scale j) ^ 2) := by
    positivity
  exact div_nonneg (le_of_lt (D.scale_pos j)) hden

private theorem xi_scan_profile_lp_peak_witness_peak_self_kernel {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) :
    xi_scan_profile_lp_peak_witness_kernel D D.peakIndex (D.gamma D.peakIndex) =
      1 / (Real.pi * D.scale D.peakIndex) := by
  have hscale_ne : D.scale D.peakIndex ≠ 0 := ne_of_gt (D.scale_pos D.peakIndex)
  calc
    xi_scan_profile_lp_peak_witness_kernel D D.peakIndex (D.gamma D.peakIndex)
        = D.scale D.peakIndex / (Real.pi * (D.scale D.peakIndex) ^ 2) := by
            simp [xi_scan_profile_lp_peak_witness_kernel]
    _ = 1 / (Real.pi * D.scale D.peakIndex) := by
          field_simp [hscale_ne, Real.pi_ne_zero]

private theorem xi_scan_profile_lp_peak_witness_peak_ratio_nonneg {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) :
    0 ≤ xi_scan_profile_lp_peak_witness_peak_ratio D := by
  unfold xi_scan_profile_lp_peak_witness_peak_ratio
  have hden : 0 < 2 * Real.pi * D.scale D.peakIndex := by
    have htwo_pi : 0 < (2 * Real.pi : ℝ) := by positivity
    exact mul_pos htwo_pi (D.scale_pos D.peakIndex)
  exact div_nonneg (D.weight_nonneg D.peakIndex) hden.le

private theorem xi_scan_profile_lp_peak_witness_peak_ratio_le_profile {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) :
    xi_scan_profile_lp_peak_witness_peak_ratio D ≤
      xi_scan_profile_lp_peak_witness_profile D (D.gamma D.peakIndex) := by
  have hsingle :
      D.weight D.peakIndex / (Real.pi * D.scale D.peakIndex) ≤
        xi_scan_profile_lp_peak_witness_profile D (D.gamma D.peakIndex) := by
    unfold xi_scan_profile_lp_peak_witness_profile
    have hsum :=
      Finset.single_le_sum
        (fun j _ =>
          mul_nonneg (D.weight_nonneg j)
            (xi_scan_profile_lp_peak_witness_kernel_nonneg D j (D.gamma D.peakIndex)))
        (by simp : D.peakIndex ∈ (Finset.univ : Finset (Fin κ)))
    have hterm :
        D.weight D.peakIndex * xi_scan_profile_lp_peak_witness_kernel D D.peakIndex
            (D.gamma D.peakIndex) =
          D.weight D.peakIndex / (Real.pi * D.scale D.peakIndex) := by
      rw [xi_scan_profile_lp_peak_witness_peak_self_kernel D]
      ring
    simpa [hterm] using hsum
  have hhalf :
      xi_scan_profile_lp_peak_witness_peak_ratio D ≤
        D.weight D.peakIndex / (Real.pi * D.scale D.peakIndex) := by
    have hscale_ne : D.scale D.peakIndex ≠ 0 := ne_of_gt (D.scale_pos D.peakIndex)
    have hnonneg :
        0 ≤ D.weight D.peakIndex / (Real.pi * D.scale D.peakIndex) := by
      have hden : 0 < Real.pi * D.scale D.peakIndex := by
        exact mul_pos Real.pi_pos (D.scale_pos D.peakIndex)
      exact div_nonneg (D.weight_nonneg D.peakIndex) hden.le
    have hrewrite :
        xi_scan_profile_lp_peak_witness_peak_ratio D =
          (1 / 2 : ℝ) * (D.weight D.peakIndex / (Real.pi * D.scale D.peakIndex)) := by
      unfold xi_scan_profile_lp_peak_witness_peak_ratio
      field_simp [Real.pi_ne_zero, hscale_ne]
    rw [hrewrite]
    nlinarith
  exact hhalf.trans hsingle

private theorem xi_scan_profile_lp_peak_witness_l2_le_mass_mul_peak_ratio {κ : ℕ}
    (D : xi_scan_profile_lp_peak_witness_data κ) :
    xi_scan_profile_lp_peak_witness_l2_diagonal_lower D ≤
      xi_scan_profile_lp_peak_witness_l1_identity D *
        xi_scan_profile_lp_peak_witness_peak_ratio D := by
  unfold xi_scan_profile_lp_peak_witness_l2_diagonal_lower
    xi_scan_profile_lp_peak_witness_l1_identity xi_scan_profile_lp_peak_witness_peak_ratio
  calc
    ∑ j : Fin κ, D.weight j ^ 2 / (2 * Real.pi * D.scale j)
        ≤ ∑ j : Fin κ, D.weight j * (D.weight D.peakIndex / (2 * Real.pi * D.scale D.peakIndex)) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hmul :=
              mul_le_mul_of_nonneg_left (D.peakIndex_max j) (D.weight_nonneg j)
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
    _ = (∑ j : Fin κ, D.weight j) * (D.weight D.peakIndex / (2 * Real.pi * D.scale D.peakIndex)) := by
          rw [Finset.sum_mul]

/-- Paper label: `prop:xi-scan-profile-lp-peak-witness`. The finite scan profile is a sum of
nonnegative Cauchy kernels, so the exact `L¹` mass is the total defect weight, the diagonal part
of the `L²` energy gives a nonnegative lower bound, and the maximizing atom produces a visible
pointwise peak whose height dominates `L² / L¹`. -/
theorem paper_xi_scan_profile_lp_peak_witness (κ : ℕ)
    (D : xi_scan_profile_lp_peak_witness_data κ) : xi_scan_profile_lp_peak_witness_holds D := by
  have hprofile_nonneg :
      ∀ x : ℝ, 0 ≤ xi_scan_profile_lp_peak_witness_profile D x := by
    intro x
    unfold xi_scan_profile_lp_peak_witness_profile
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (D.weight_nonneg j) (xi_scan_profile_lp_peak_witness_kernel_nonneg D j x)
  have hl2_nonneg : 0 ≤ xi_scan_profile_lp_peak_witness_l2_diagonal_lower D := by
    unfold xi_scan_profile_lp_peak_witness_l2_diagonal_lower
    refine Finset.sum_nonneg ?_
    intro j hj
    have hden : 0 < 2 * Real.pi * D.scale j := by
      have htwo_pi : 0 < (2 * Real.pi : ℝ) := by positivity
      exact mul_pos htwo_pi (D.scale_pos j)
    exact div_nonneg (sq_nonneg (D.weight j)) hden.le
  have hmass_nonneg : 0 ≤ xi_scan_profile_lp_peak_witness_l1_identity D := by
    exact le_of_lt D.totalMass_pos
  have hpeak_mul :
      xi_scan_profile_lp_peak_witness_l2_diagonal_lower D ≤
        xi_scan_profile_lp_peak_witness_l1_identity D *
          xi_scan_profile_lp_peak_witness_profile D (D.gamma D.peakIndex) := by
    have hpeak_ratio := xi_scan_profile_lp_peak_witness_peak_ratio_le_profile D
    exact
      (xi_scan_profile_lp_peak_witness_l2_le_mass_mul_peak_ratio D).trans
        (mul_le_mul_of_nonneg_left hpeak_ratio hmass_nonneg)
  have hpeak :
      xi_scan_profile_lp_peak_witness_l2_diagonal_lower D /
          xi_scan_profile_lp_peak_witness_l1_identity D ≤
        xi_scan_profile_lp_peak_witness_profile D (D.gamma D.peakIndex) := by
    exact (_root_.div_le_iff₀ D.totalMass_pos).2 (by simpa [mul_comm] using hpeak_mul)
  exact ⟨hprofile_nonneg, D.totalMass_pos, hl2_nonneg, hpeak⟩

end

end Omega.Zeta
