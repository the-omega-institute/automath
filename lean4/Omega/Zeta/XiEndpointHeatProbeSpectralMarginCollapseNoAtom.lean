import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Central-binomial normalization scale for the endpoint heat-probe bound. -/
noncomputable def xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale
    (N : ℕ) : ℝ :=
  (4 : ℝ) ^ N / (Nat.choose (2 * N) N : ℝ)

/-- Concrete monotone-limit/spectral-margin data for the no-endpoint-atom collapse. -/
structure xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_Data where
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom : ℝ
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass : ℕ → ℝ
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_toeplitzMin : ℕ → ℝ
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_noEndpointAtom :
    xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom = 0
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass_tendsto :
    Tendsto xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass atTop
      (𝓝 xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom)
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_scaledBound_tendsto_zero :
    xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom = 0 →
      Tendsto
        (fun N : ℕ =>
          xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass N *
            xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale N)
        atTop (𝓝 0)
  xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_spectral_margin_bound :
    ∀ N,
      xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_toeplitzMin N ≤
        xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass N *
          xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale N

/-- In the no-atom case, the normalized spectral-margin bound forces arbitrary small margins. -/
def xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_statement
    (D : xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_Data) : Prop :=
  D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom = 0 ∧
    Tendsto D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass atTop
      (𝓝 D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointAtom) ∧
    Tendsto
      (fun N : ℕ =>
        D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass N *
          xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale N)
      atTop (𝓝 0) ∧
    ∀ ε > 0,
      ∀ᶠ N in atTop,
        D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_toeplitzMin N ≤ ε

/-- Paper label: `cor:xi-endpoint-heat-probe-spectral-margin-collapse-no-atom`. -/
theorem paper_xi_endpoint_heat_probe_spectral_margin_collapse_no_atom
    (D : xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_Data) :
    xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_statement D := by
  refine ⟨D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_noEndpointAtom,
    D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass_tendsto, ?_, ?_⟩
  · exact D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_scaledBound_tendsto_zero
      D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_noEndpointAtom
  · intro ε hε
    have hscaled :
        Tendsto
          (fun N : ℕ =>
            D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass N *
              xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale N)
          atTop (𝓝 0) :=
      D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_scaledBound_tendsto_zero
        D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_noEndpointAtom
    have hsmall :
        ∀ᶠ N in atTop,
          D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_endpointMass N *
              xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_centralScale N < ε :=
      hscaled.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with N hN
    exact le_trans
      (D.xi_endpoint_heat_probe_spectral_margin_collapse_no_atom_spectral_margin_bound N)
      (le_of_lt hN)

end Omega.Zeta
