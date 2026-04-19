import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonEntropyTomography
import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointOrthogonal
import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete boundary-layer data for the unblinding alternatives. The fixed-chart obstruction is
measured through the boundary verifier, comoving localization uses the aligned-chart depth law,
and reversible tomography is packaged by the entropy-moment identities. -/
structure BoundaryUnblindPathsData where
  δ : ℝ
  γ : ℝ
  hδ : 0 < δ
  verifier : BoundaryJointVerifierData
  endpointHeat : BoundaryEndpointHeatData
  A4 : ℝ
  A6 : ℝ
  B6 : ℝ
  sigmaSq : ℝ
  mu3Sq : ℝ
  mu4 : ℝ
  hsigma : sigmaSq ≠ 0
  hA4 : 8 * A4 = sigmaSq ^ 2
  hA6 : 64 * A6 = sigmaSq ^ 3 - 8 * sigmaSq * mu4 + 6 * mu3Sq
  hB6 : 32 * B6 = 3 * mu3Sq

/-- Comoving localization removes the fixed-chart blindspot and exposes a strictly positive depth
at the aligned chart. -/
def BoundaryUnblindPathsData.comovingLocalizationUnblinds
    (D : BoundaryUnblindPathsData) : Prop :=
  typedAddressComovingChartDepth D.δ D.γ D.γ = (4 * D.δ) / (1 + D.δ) ^ 2 ∧
    0 < typedAddressComovingChartDepth D.δ D.γ D.γ

/-- Reversible tomography unblinds the boundary data by recovering the second-, third-, and
fourth-order moment parameters from the audited entropy-moment coordinates. -/
def BoundaryUnblindPathsData.tomographicReencodingUnblinds
    (D : BoundaryUnblindPathsData) : Prop :=
  D.sigmaSq ^ 2 = 8 * D.A4 ∧
    D.mu3Sq = (32 / 3) * D.B6 ∧
    D.mu4 = (D.sigmaSq ^ 3 + 6 * D.mu3Sq - 64 * D.A6) / (8 * D.sigmaSq)

/-- Fixed-chart refinement does not remove the boundary obstruction: the fixed-chart depth obeys
the usual quadratic law, and the endpoint-heat axis remains logically non-substitutable. -/
def BoundaryUnblindPathsData.noFixedChartRefinementUnblinds
    (D : BoundaryUnblindPathsData) : Prop :=
  typedAddressFixedChartDepth D.δ D.γ = (4 * D.δ) / (D.γ ^ 2 + (1 + D.δ) ^ 2) ∧
    ((D.verifier.axes.radiusBlindspotClosed ∧ D.verifier.axes.addressCollisionClosed ∧
        ¬ D.verifier.axes.endpointHeatClosed) →
      D.verifier.verifierResult ≠ BoundaryVerifierResult.certificate)

/-- At the boundary blindspot, fixed-chart refinements cannot remove the endpoint obstruction,
while the admissible unblinding exits are the comoving localization route and the reversible
tomographic reencoding route.
    prop:typed-address-biaxial-completion-boundary-unblind-paths -/
theorem paper_typed_address_biaxial_completion_boundary_unblind_paths
    (D : BoundaryUnblindPathsData) :
    D.comovingLocalizationUnblinds ∧
      D.tomographicReencodingUnblinds ∧
      D.noFixedChartRefinementUnblinds := by
  have hFirstOrder :
      typedAddressFixedChartDepth D.δ D.γ = (4 * D.δ) / (D.γ ^ 2 + (1 + D.δ) ^ 2) ∧
        typedAddressComovingChartDepth D.δ D.γ D.γ = (4 * D.δ) / (1 + D.δ) ^ 2 :=
    paper_typed_address_biaxial_completion_comoving_first_order
      (δ := D.δ) (γ := D.γ) (le_of_lt D.hδ)
  have hTomography :
      D.sigmaSq ^ 2 = 8 * D.A4 ∧
        D.mu3Sq = (32 / 3) * D.B6 ∧
        D.mu4 = (D.sigmaSq ^ 3 + 6 * D.mu3Sq - 64 * D.A6) / (8 * D.sigmaSq) :=
    Omega.CircleDimension.paper_cdim_poisson_entropy_moment_tomography
      D.hsigma D.hA4 D.hA6 D.hB6
  have hEndpointAxis :
      (D.verifier.axes.radiusBlindspotClosed ∧ D.verifier.axes.addressCollisionClosed ∧
          ¬ D.verifier.axes.endpointHeatClosed) →
        D.verifier.verifierResult ≠ BoundaryVerifierResult.certificate :=
    (paper_typed_address_biaxial_completion_boundary_endpoint_orthogonal
      D.verifier D.endpointHeat).2
  refine ⟨?_, hTomography, ?_⟩
  · refine ⟨hFirstOrder.2, ?_⟩
    rw [hFirstOrder.2]
    have hNum : 0 < 4 * D.δ := by
      nlinarith [D.hδ]
    have hDenBase : 0 < 1 + D.δ := by
      linarith
    exact div_pos hNum (sq_pos_of_pos hDenBase)
  · exact ⟨hFirstOrder.1, hEndpointAxis⟩

end Omega.TypedAddressBiaxialCompletion
