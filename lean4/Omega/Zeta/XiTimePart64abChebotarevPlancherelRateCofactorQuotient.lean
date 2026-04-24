import Omega.Zeta.FiniteRhPhaseLiftArtin
import Omega.Zeta.XiTimePart64CoverPerronRootTrivialChannel

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Paper label: `thm:xi-time-part64ab-artin-cofactor-nearest-zero-radius`. Once the Artin
determinant factorization has been recorded, the nearest zero radius of the nontrivial cofactor is
the reciprocal of the maximal nontrivial channel radius, and this reciprocal is uniquely
characterized by the equation `z * ρ = 1`. -/
theorem paper_xi_time_part64ab_artin_cofactor_nearest_zero_radius
    (D : FiniteRhPhaseLiftArtinData) {κ n : ℕ}
    (blocks : Fin κ → Matrix (Fin n) (Fin n) ℕ)
    (hρpos : 0 <
      Finset.univ.sup fun χ : Fin κ =>
        xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ)) :
    D.artinDeterminantFactorization ∧
      let nontrivialSpectralRadius :=
        Finset.univ.sup fun χ : Fin κ =>
          xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ)
      let nearestZeroRadius : ℚ := (nontrivialSpectralRadius : ℚ)⁻¹
      nearestZeroRadius * nontrivialSpectralRadius = 1 ∧
        ∀ z : ℚ, z * nontrivialSpectralRadius = 1 → z = nearestZeroRadius := by
  let paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius : ℕ :=
    Finset.univ.sup fun χ : Fin κ =>
      xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ)
  have hρpos' :
      0 < paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius := by
    simpa [paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius]
      using hρpos
  have hρqpos :
      (0 :
        ℚ) < paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius := by
    exact_mod_cast hρpos'
  refine ⟨(paper_finite_rh_phase_lift_artin D).1, ?_⟩
  change
    ((paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
        ℚ)⁻¹ *
        (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
          ℚ) =
      1) ∧
      ∀ z : ℚ,
        z *
            (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
              ℚ) =
          1 →
          z =
            (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
              ℚ)⁻¹
  constructor
  · field_simp [hρqpos.ne']
  · intro z hz
    calc
      z =
          z *
            ((paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
                ℚ) *
              (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
                ℚ)⁻¹) := by field_simp [hρqpos.ne']
      _ =
          (z *
              (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
                ℚ)) *
            (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
              ℚ)⁻¹ := by ring
      _ = 1 *
            (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
              ℚ)⁻¹ := by rw [hz]
      _ =
          (paper_label_xi_time_part64ab_artin_cofactor_nearest_zero_radius_nontrivialSpectralRadius :
            ℚ)⁻¹ := by ring

end Omega.Zeta
