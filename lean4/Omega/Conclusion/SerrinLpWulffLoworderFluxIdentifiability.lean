import Mathlib.Tactic
import Omega.SPG.LpSuperellipsoidBoundaryVolumeDecoding

namespace Omega.Conclusion

/-- Concrete data for the normalized low-order Serrin/Wulff flux decoder.  The axes `a`,
dimension, exponent, and volume are the actual diagonal `L^p` superellipsoid parameters; the
hypotheses keep the volume-normalized Serrin regime in the range covered by the SPG decoder. -/
structure conclusion_serrin_lp_wulff_loworder_flux_identifiability_data where
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension : ℕ
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent : ℕ
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_axes :
    Fin conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension → ℝ
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume : ℝ
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension_ge_two :
    2 ≤ conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent_gt_one :
    1 < conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume_pos :
    0 < conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume
  conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume_normalized :
    conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume = 1

/-- The zeroth low-order flux attached to the normalized Serrin/Wulff package. -/
def conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.zerothFlux
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data) : ℝ :=
  Omega.SPG.lpSuperellipsoidBoundaryFlux0
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume

/-- The coordinate low-order fluxes attached to the normalized Serrin/Wulff package. -/
def conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.coordinateFlux
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data)
    (i : Fin D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension) : ℝ :=
  Omega.SPG.lpSuperellipsoidBoundaryFlux
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_axes i

/-- The decoded normalized volume from the zeroth low-order flux. -/
noncomputable def conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.decodedVolume
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data) : ℝ :=
  Omega.SPG.lpSuperellipsoidDecodedVolume
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension D.zerothFlux

/-- The decoded coordinate axis powers from the low-order flux ratios. -/
noncomputable def conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.decodedAxisPower
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data)
    (i : Fin D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension) : ℝ :=
  Omega.SPG.lpSuperellipsoidDecodedAxisPower
    D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension D.zerothFlux
    (D.coordinateFlux i)

/-- Paper-facing conclusion: low-order fluxes recover the normalized volume and all axis powers. -/
noncomputable def conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.Holds
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data) : Prop :=
  D.decodedVolume = 1 ∧
    ∀ i : Fin D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension,
      D.decodedAxisPower i =
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_axes i ^
          D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent

/-- Paper label: `cor:conclusion-serrin-lp-wulff-loworder-flux-identifiability`. -/
theorem paper_conclusion_serrin_lp_wulff_loworder_flux_identifiability
    (D : conclusion_serrin_lp_wulff_loworder_flux_identifiability_data) : D.Holds := by
  rcases
      Omega.SPG.paper_spg_lp_superellipsoid_boundary_volume_decoding
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_axes
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_dimension_ge_two
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_exponent_gt_one
        D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume_pos with
    ⟨hVolume, _hFlux, hAxis⟩
  refine ⟨?_, ?_⟩
  · simpa [
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.Holds,
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.decodedVolume,
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.zerothFlux,
      D.conclusion_serrin_lp_wulff_loworder_flux_identifiability_volume_normalized] using hVolume
  · intro i
    simpa [
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.Holds,
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.decodedAxisPower,
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.coordinateFlux,
      conclusion_serrin_lp_wulff_loworder_flux_identifiability_data.zerothFlux] using hAxis i

end Omega.Conclusion
