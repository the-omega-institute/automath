import Omega.SPG.ErrorThreshold
import Omega.SPG.EllipsoidFluxDecodingPerturbationStability
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing wrapper for exact exponent recovery under the relative error threshold.
    thm:spg-godel-boundary-decoding-relative-error-threshold -/
theorem paper_spg_godel_boundary_decoding_relative_error_threshold (ε pmin : ℝ)
    (exactDecoding : Prop) (hε : 0 < ε) (hpmin : 1 < pmin)
    (hThreshold : ε < (pmin - 1) / (pmin + 1))
    (hDecode : ε < (pmin - 1) / (pmin + 1) -> exactDecoding) : exactDecoding := by
  have hε_lt_one : ε < 1 := by
    have hpmin1 : 0 < pmin + 1 := by linarith
    have hcut : (pmin - 1) / (pmin + 1) < 1 := by
      rw [div_lt_iff₀ hpmin1]
      linarith
    linarith
  have hkappa : kappa ε < pmin := (kappa_lt_iff_eps_lt hpmin hε hε_lt_one).2 hThreshold
  have hExact : exactDecoding := hDecode hThreshold
  have hStable :
      exactDecoding ∧ kappa ε < pmin :=
    paper_spg_ellipsoid_flux_decoding_perturbation_stability 1 exactDecoding (kappa ε < pmin)
      hExact (fun _ => hkappa)
  exact hStable.1

end Omega.SPG
