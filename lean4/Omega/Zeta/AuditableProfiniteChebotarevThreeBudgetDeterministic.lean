import Mathlib.Tactic
import Omega.Experiments.TVCertificateHist
import Omega.Zeta.AuditableProfiniteChebotarevFinite

namespace Omega.Zeta

open Omega.Experiments.MarkovTVSampleComplexity

noncomputable section

/-- Concrete data for the deterministic three-budget Chebotarev inequality. The finite
Chebotarev certificate supplies the deterministic tail and observable-vs-TV comparison, while the
Sturmian pushforward step is recorded as a star-discrepancy control of the folded TV distance. -/
structure auditable_profinite_chebotarev_three_budget_deterministic_data where
  m : ℕ
  n : ℝ
  N : ℝ
  stateCount : ℝ
  delta : ℝ
  gammaPs : ℝ
  lambda : ℝ
  eps : ℝ
  K1 : ℝ
  K2 : ℝ
  tvMicro : ℝ
  tvFold : ℝ
  observedError : ℝ
  tail : ℝ
  star : ℝ
  hK2 : 0 ≤ K2
  hStateCount : stateCount = 2 * (m + 1 : ℝ)
  hEnvelope : markovTvEnvelopeRadius N stateCount delta gammaPs = star
  hTail :
    tail =
      auditableProfiniteChebotarevDeterministicTerm
        (K1 * stateCount) ((1 / 2 : ℝ) + eps) lambda n
  hMicro : tvMicro ≤ (m + 1 : ℝ) * star
  hFold : tvFold ≤ tvMicro
  hIndicator : observedError ≤ tail + K2 * tvFold

namespace auditable_profinite_chebotarev_three_budget_deterministic_data

/-- The target deterministic three-budget inequality. -/
def holds (D : auditable_profinite_chebotarev_three_budget_deterministic_data) : Prop :=
  D.observedError ≤
    auditableProfiniteChebotarevDeterministicTerm
        (D.K1 * D.stateCount) ((1 / 2 : ℝ) + D.eps) D.lambda D.n +
      D.K2 * ((D.m + 1 : ℝ) * D.star)

/-- The underlying finite-data Chebotarev certificate, reconstructed after substituting the
Sturmian TV budget into the Markov-TV envelope term. -/
def auditable_profinite_chebotarev_three_budget_deterministic_toFiniteData
    (D : auditable_profinite_chebotarev_three_budget_deterministic_data) :
    AuditableProfiniteChebotarevFiniteData :=
  { n := D.n
    N := D.N
    stateCount := D.stateCount
    delta := D.delta
    gammaPs := D.gammaPs
    lambda := D.lambda
    eps := D.eps
    K1 := D.K1
    K2 := D.K2
    dtv := D.tvFold
    observedError := D.observedError
    tail := D.tail
    hK2 := D.hK2
    hTail := D.hTail
    hTv := by
      obtain ⟨_, htvFold⟩ :=
        Omega.Experiments.TVCertificateHist.paper_tv_certificate_hist
          D.m D.tvMicro D.tvFold D.star D.hMicro D.hFold
      calc
        D.tvFold ≤ (D.m + 1 : ℝ) * D.star := htvFold
        _ = (D.stateCount / 2) * markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs := by
          rw [← D.hEnvelope]
          rw [D.hStateCount]
          ring
    hIndicator := D.hIndicator }

end auditable_profinite_chebotarev_three_budget_deterministic_data

open auditable_profinite_chebotarev_three_budget_deterministic_data

/-- Paper label: `cor:auditable-profinite-chebotarev-three-budget-deterministic`. The finite
Chebotarev certificate gives the deterministic tail plus a TV term, and the Sturmian pushforward
estimate replaces that TV term by the explicit star-discrepancy budget `(m + 1) D_N^*`. -/
theorem paper_auditable_profinite_chebotarev_three_budget_deterministic
    (D : auditable_profinite_chebotarev_three_budget_deterministic_data) : D.holds := by
  have hfinite :
      D.observedError ≤
        auditableProfiniteChebotarevDeterministicTerm
            (D.K1 * D.stateCount) ((1 / 2 : ℝ) + D.eps) D.lambda D.n +
          D.K2 *
            (D.stateCount / 2 *
              markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs) := by
    simpa [auditable_profinite_chebotarev_three_budget_deterministic_toFiniteData,
      AuditableProfiniteChebotarevFiniteData.Holds] using
      paper_auditable_profinite_chebotarev_finite
        D.auditable_profinite_chebotarev_three_budget_deterministic_toFiniteData
  calc
    D.observedError ≤
        auditableProfiniteChebotarevDeterministicTerm
            (D.K1 * D.stateCount) ((1 / 2 : ℝ) + D.eps) D.lambda D.n +
          D.K2 *
            (D.stateCount / 2 *
              markovTvEnvelopeRadius D.N D.stateCount D.delta D.gammaPs) := hfinite
    _ = auditableProfiniteChebotarevDeterministicTerm
          (D.K1 * D.stateCount) ((1 / 2 : ℝ) + D.eps) D.lambda D.n +
        D.K2 * ((D.m + 1 : ℝ) * D.star) := by
          rw [← D.hEnvelope]
          rw [D.hStateCount]
          ring

end

end Omega.Zeta
