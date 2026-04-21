import Mathlib.Tactic
import Omega.Experiments.MarkovTVSampleComplexity
import Omega.Zeta.AuditableProfiniteChebotarevTradeoff

namespace Omega.Zeta

open Omega.Experiments.MarkovTVSampleComplexity

noncomputable section

/-- Finite-data certificate for the auditable profinite Chebotarev bound. The record contains the
explicit deterministic tail, the Markov-TV envelope, and the Lipschitz comparison of the cylinder
observable against TV. -/
structure AuditableProfiniteChebotarevFiniteData where
  n : ℝ
  N : ℝ
  stateCount : ℝ
  delta : ℝ
  gammaPs : ℝ
  lambda : ℝ
  eps : ℝ
  K1 : ℝ
  K2 : ℝ
  dtv : ℝ
  observedError : ℝ
  tail : ℝ
  hK2 : 0 ≤ K2
  hTail :
    tail =
      auditableProfiniteChebotarevDeterministicTerm
        (K1 * stateCount) ((1 / 2 : ℝ) + eps) lambda n
  hTv :
    dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs
  hIndicator :
    observedError ≤ tail + K2 * dtv

namespace AuditableProfiniteChebotarevFiniteData

/-- Final finite-data Chebotarev certificate after composing the deterministic tail with the
Markov-TV envelope through the observable-vs-TV comparison. -/
def Holds (D : AuditableProfiniteChebotarevFiniteData) : Prop :=
  D.observedError ≤
    auditableProfiniteChebotarevDeterministicTerm
        (D.K1 * D.stateCount) ((1 / 2 : ℝ) + D.eps) D.lambda D.n +
      D.K2 *
        ((D.stateCount / 2) *
          markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs)

end AuditableProfiniteChebotarevFiniteData

open AuditableProfiniteChebotarevFiniteData

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:auditable-profinite-chebotarev-finite`. The deterministic twisted-spectrum
tail, the Markov-TV envelope, and the Lipschitz comparison for cylinder observables combine by one
triangle-inequality step into the explicit finite-data certificate. -/
theorem paper_auditable_profinite_chebotarev_finite
    (D : AuditableProfiniteChebotarevFiniteData) : D.Holds := by
  have hcomp :
      D.observedError ≤
        D.tail +
          D.K2 *
            ((D.stateCount / 2) *
              markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs) := by
    have hmul :
        D.K2 * D.dtv ≤
          D.K2 *
            ((D.stateCount / 2) *
              markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs) := by
      exact mul_le_mul_of_nonneg_left D.hTv D.hK2
    calc
      D.observedError ≤ D.tail + D.K2 * D.dtv := D.hIndicator
      _ ≤ D.tail +
            D.K2 *
              ((D.stateCount / 2) *
                markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs) := by
            linarith
  simpa [AuditableProfiniteChebotarevFiniteData.Holds, D.hTail] using hcomp

end

end Omega.Zeta
