import Mathlib.Tactic
import Omega.SPG.EllipsoidBoundaryFluxReconstruction

namespace Omega.Conclusion

/-- Conclusion-level rigid ellipsoid package with barycenter normalization. -/
structure conclusion_serrin_ellipsoid_flux_identifiability_data where
  conclusion_serrin_ellipsoid_flux_identifiability_dimension : ℕ
  conclusion_serrin_ellipsoid_flux_identifiability_dimension_pos :
    0 < conclusion_serrin_ellipsoid_flux_identifiability_dimension
  conclusion_serrin_ellipsoid_flux_identifiability_volume : ℝ
  conclusion_serrin_ellipsoid_flux_identifiability_B0 : ℝ
  conclusion_serrin_ellipsoid_flux_identifiability_B :
    Fin conclusion_serrin_ellipsoid_flux_identifiability_dimension →
      Fin conclusion_serrin_ellipsoid_flux_identifiability_dimension → ℝ
  conclusion_serrin_ellipsoid_flux_identifiability_Q :
    Fin conclusion_serrin_ellipsoid_flux_identifiability_dimension →
      Fin conclusion_serrin_ellipsoid_flux_identifiability_dimension → ℝ
  conclusion_serrin_ellipsoid_flux_identifiability_barycenter :
    Fin conclusion_serrin_ellipsoid_flux_identifiability_dimension → ℝ
  conclusion_serrin_ellipsoid_flux_identifiability_barycenter_eq_zero :
    conclusion_serrin_ellipsoid_flux_identifiability_barycenter = 0
  conclusion_serrin_ellipsoid_flux_identifiability_boundary_mass :
    conclusion_serrin_ellipsoid_flux_identifiability_B0 =
      (conclusion_serrin_ellipsoid_flux_identifiability_dimension : ℝ) *
        conclusion_serrin_ellipsoid_flux_identifiability_volume
  conclusion_serrin_ellipsoid_flux_identifiability_boundary_mass_ne :
    conclusion_serrin_ellipsoid_flux_identifiability_B0 ≠ 0
  conclusion_serrin_ellipsoid_flux_identifiability_boundary_tensor :
    ∀ i j,
      conclusion_serrin_ellipsoid_flux_identifiability_B i j =
        conclusion_serrin_ellipsoid_flux_identifiability_volume *
          conclusion_serrin_ellipsoid_flux_identifiability_Q i j
  conclusion_serrin_ellipsoid_flux_identifiability_volume_normalized :
    conclusion_serrin_ellipsoid_flux_identifiability_volume = 1

namespace conclusion_serrin_ellipsoid_flux_identifiability_data

/-- The centered ellipsoid is reconstructed directly from the finitely many boundary fluxes, and
volume normalization collapses the decoding scale factor to `1`. -/
def reconstructs_Q_from_boundary_fluxes
    (D : conclusion_serrin_ellipsoid_flux_identifiability_data) : Prop :=
  D.conclusion_serrin_ellipsoid_flux_identifiability_barycenter = 0 ∧
    D.conclusion_serrin_ellipsoid_flux_identifiability_volume = 1 ∧
    D.conclusion_serrin_ellipsoid_flux_identifiability_B0 =
      (D.conclusion_serrin_ellipsoid_flux_identifiability_dimension : ℝ) ∧
    ∀ i j,
      D.conclusion_serrin_ellipsoid_flux_identifiability_Q i j =
        D.conclusion_serrin_ellipsoid_flux_identifiability_B i j

end conclusion_serrin_ellipsoid_flux_identifiability_data

open conclusion_serrin_ellipsoid_flux_identifiability_data

/-- Paper label: `thm:conclusion-serrin-ellipsoid-flux-identifiability`. Centering at the
barycenter leaves a rigid ellipsoid model, the SPG boundary-flux reconstruction theorem recovers
`Q = (n / B₀) B`, and the volume-normalization hypothesis forces `B₀ = n`, hence the scale factor
is `1` and the boundary tensor itself equals the recovered matrix. -/
theorem paper_conclusion_serrin_ellipsoid_flux_identifiability
    (D : conclusion_serrin_ellipsoid_flux_identifiability_data) :
    D.reconstructs_Q_from_boundary_fluxes := by
  rcases
      Omega.SPG.paper_spg_ellipsoid_boundary_flux_reconstruction
        D.conclusion_serrin_ellipsoid_flux_identifiability_dimension
        D.conclusion_serrin_ellipsoid_flux_identifiability_dimension_pos
        D.conclusion_serrin_ellipsoid_flux_identifiability_volume
        D.conclusion_serrin_ellipsoid_flux_identifiability_B0
        D.conclusion_serrin_ellipsoid_flux_identifiability_B
        D.conclusion_serrin_ellipsoid_flux_identifiability_Q
        D.conclusion_serrin_ellipsoid_flux_identifiability_boundary_mass
        D.conclusion_serrin_ellipsoid_flux_identifiability_boundary_mass_ne
        D.conclusion_serrin_ellipsoid_flux_identifiability_boundary_tensor with
    ⟨_hvolume, hQ⟩
  have hB0 :
      D.conclusion_serrin_ellipsoid_flux_identifiability_B0 =
        (D.conclusion_serrin_ellipsoid_flux_identifiability_dimension : ℝ) := by
    rw [D.conclusion_serrin_ellipsoid_flux_identifiability_boundary_mass,
      D.conclusion_serrin_ellipsoid_flux_identifiability_volume_normalized]
    ring
  refine
    ⟨D.conclusion_serrin_ellipsoid_flux_identifiability_barycenter_eq_zero,
      D.conclusion_serrin_ellipsoid_flux_identifiability_volume_normalized, hB0, ?_⟩
  intro i j
  specialize hQ i j
  have hd_ne :
      (D.conclusion_serrin_ellipsoid_flux_identifiability_dimension : ℝ) ≠ 0 := by
    exact_mod_cast
      Nat.ne_of_gt D.conclusion_serrin_ellipsoid_flux_identifiability_dimension_pos
  rw [hB0] at hQ
  rw [div_self hd_ne, one_mul] at hQ
  exact hQ

end Omega.Conclusion
