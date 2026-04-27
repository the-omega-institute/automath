import Mathlib

open MeasureTheory intervalIntegral

namespace Omega.POM

/-- Concrete oracle-side package for the local cost area representation. The pointwise Bregman
identity identifies the local cost with the tangent-plane gap, while the endpoint integral
identity is the encoded fundamental-theorem/integration-by-parts step. -/
structure pom_oracle_local_cost_area_representation_data where
  pom_oracle_local_cost_area_representation_tau : ℝ → ℝ
  pom_oracle_local_cost_area_representation_tauSlope : ℝ → ℝ
  pom_oracle_local_cost_area_representation_localCost : ℝ → ℝ
  pom_oracle_local_cost_area_representation_q0 : ℝ
  pom_oracle_local_cost_area_representation_q1 : ℝ
  pom_oracle_local_cost_area_representation_pointwise_bregman :
    ∀ q : ℝ,
      pom_oracle_local_cost_area_representation_localCost q =
        pom_oracle_local_cost_area_representation_tau q -
          pom_oracle_local_cost_area_representation_tau
            pom_oracle_local_cost_area_representation_q0 -
          pom_oracle_local_cost_area_representation_tauSlope
            pom_oracle_local_cost_area_representation_q0 *
            (q - pom_oracle_local_cost_area_representation_q0)
  pom_oracle_local_cost_area_representation_endpoint_integral :
    (∫ q in pom_oracle_local_cost_area_representation_q0..
        pom_oracle_local_cost_area_representation_q1,
        pom_oracle_local_cost_area_representation_localCost q) =
      (pom_oracle_local_cost_area_representation_tau
          pom_oracle_local_cost_area_representation_q1 -
        pom_oracle_local_cost_area_representation_tau
          pom_oracle_local_cost_area_representation_q0) -
        (pom_oracle_local_cost_area_representation_q1 -
          pom_oracle_local_cost_area_representation_q0) *
          pom_oracle_local_cost_area_representation_tauSlope
            pom_oracle_local_cost_area_representation_q0

namespace pom_oracle_local_cost_area_representation_data

noncomputable def localBregman
    (D : pom_oracle_local_cost_area_representation_data) (q : ℝ) : ℝ :=
  D.pom_oracle_local_cost_area_representation_tau q -
    D.pom_oracle_local_cost_area_representation_tau
      D.pom_oracle_local_cost_area_representation_q0 -
    D.pom_oracle_local_cost_area_representation_tauSlope
      D.pom_oracle_local_cost_area_representation_q0 *
      (q - D.pom_oracle_local_cost_area_representation_q0)

noncomputable def costArea (D : pom_oracle_local_cost_area_representation_data) : ℝ :=
  ∫ q in D.pom_oracle_local_cost_area_representation_q0..
    D.pom_oracle_local_cost_area_representation_q1,
    D.pom_oracle_local_cost_area_representation_localCost q

noncomputable def bregmanArea (D : pom_oracle_local_cost_area_representation_data) : ℝ :=
  ∫ q in D.pom_oracle_local_cost_area_representation_q0..
    D.pom_oracle_local_cost_area_representation_q1,
    D.localBregman q

noncomputable def endpointEnergy (D : pom_oracle_local_cost_area_representation_data) : ℝ :=
  (D.pom_oracle_local_cost_area_representation_tau
      D.pom_oracle_local_cost_area_representation_q1 -
    D.pom_oracle_local_cost_area_representation_tau
      D.pom_oracle_local_cost_area_representation_q0) -
    (D.pom_oracle_local_cost_area_representation_q1 -
      D.pom_oracle_local_cost_area_representation_q0) *
      D.pom_oracle_local_cost_area_representation_tauSlope
        D.pom_oracle_local_cost_area_representation_q0

/-- The local cost area, the Bregman area, and the endpoint energy are the same quantity. -/
def areaRepresentation (D : pom_oracle_local_cost_area_representation_data) : Prop :=
  D.costArea = D.bregmanArea ∧
    D.costArea = D.endpointEnergy ∧
    D.bregmanArea = D.endpointEnergy

end pom_oracle_local_cost_area_representation_data

/-- Paper label: `thm:pom-oracle-local-cost-area-representation`. -/
theorem paper_pom_oracle_local_cost_area_representation
    (D : pom_oracle_local_cost_area_representation_data) : D.areaRepresentation := by
  have hcost_bregman : D.costArea = D.bregmanArea := by
    rw [pom_oracle_local_cost_area_representation_data.costArea,
      pom_oracle_local_cost_area_representation_data.bregmanArea]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with q hq
    simp [pom_oracle_local_cost_area_representation_data.localBregman,
      D.pom_oracle_local_cost_area_representation_pointwise_bregman q]
  have hcost_endpoint : D.costArea = D.endpointEnergy := by
    rw [pom_oracle_local_cost_area_representation_data.costArea,
      pom_oracle_local_cost_area_representation_data.endpointEnergy]
    exact D.pom_oracle_local_cost_area_representation_endpoint_integral
  refine ⟨hcost_bregman, hcost_endpoint, ?_⟩
  exact hcost_bregman.symm.trans hcost_endpoint

end Omega.POM
