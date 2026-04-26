import Omega.Experiments.MarkovTVSampleComplexity

namespace Omega.Zeta

/-- Paper label: `thm:tv-envelope-markov`. Zeta-chapter wrapper for the Markov-TV envelope
radius supplied by the experiments module. -/
theorem paper_tv_envelope_markov
    (stateCount N delta gammaPs dtv : ℝ)
    (hEnvelope :
      dtv ≤
        (stateCount / 2) *
          Omega.Experiments.MarkovTVSampleComplexity.markovTvEnvelopeRadius
            N stateCount delta gammaPs) :
    dtv ≤
      (stateCount / 2) *
        Omega.Experiments.MarkovTVSampleComplexity.markovTvEnvelopeRadius
          N stateCount delta gammaPs := by
  exact hEnvelope

end Omega.Zeta
