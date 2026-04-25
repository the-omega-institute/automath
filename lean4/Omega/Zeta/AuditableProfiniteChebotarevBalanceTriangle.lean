import Mathlib.Tactic
import Omega.Zeta.AuditableProfiniteChebotarevFinite

namespace Omega.Zeta

open Omega.Experiments.MarkovTVSampleComplexity

noncomputable section

/-- Concrete half-budget closure for the auditable profinite Chebotarev certificate. -/
def auditable_profinite_chebotarev_balance_triangle_statement : Prop :=
  ∀ {n N stateCount delta gammaPs lambda eps K1 K2 dtv observedError tail tau : ℝ},
    0 ≤ K2 →
    tail =
      auditableProfiniteChebotarevDeterministicTerm
        (K1 * stateCount) ((1 / 2 : ℝ) + eps) lambda n →
    dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs →
    observedError ≤ tail + K2 * dtv →
    auditableProfiniteChebotarevDeterministicTerm
        (K1 * stateCount) ((1 / 2 : ℝ) + eps) lambda n ≤ tau / 2 →
    K2 * ((stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs) ≤ tau / 2 →
    observedError ≤ tau

/-- Paper label: `cor:auditable-profinite-chebotarev-balance-triangle`. The finite Chebotarev
certificate already decomposes the observable error into a deterministic tail and a TV-driven
sampling term; imposing the two half-budget hypotheses gives the final `tau`-bound by one
additive estimate. -/
theorem paper_auditable_profinite_chebotarev_balance_triangle :
    auditable_profinite_chebotarev_balance_triangle_statement := by
  intro n N stateCount delta gammaPs lambda eps K1 K2 dtv observedError tail tau hK2 htail htv
    hindicator hdet_half hsample_half
  let D : AuditableProfiniteChebotarevFiniteData :=
    { n := n
      N := N
      stateCount := stateCount
      delta := delta
      gammaPs := gammaPs
      lambda := lambda
      eps := eps
      K1 := K1
      K2 := K2
      dtv := dtv
      observedError := observedError
      tail := tail
      hK2 := hK2
      hTail := htail
      hTv := htv
      hIndicator := hindicator }
  have hfinite := paper_auditable_profinite_chebotarev_finite D
  unfold AuditableProfiniteChebotarevFiniteData.Holds at hfinite
  linarith

end

end Omega.Zeta
