import Mathlib.Tactic

namespace Omega.GU

/-- Witness package for the PF derivative identity used to define the paper's `β`. -/
structure BetaPfExpectationWitness where
  beta : ℝ
  baseSpectrumDerivative : ℝ
  channelPfExpectation : ℝ
  derivativeIdentity : beta = baseSpectrumDerivative - channelPfExpectation

/-- Chapter-local wrapper exposing the audited base-spectrum derivative, the PF expectation term,
and a witness that identifies `β` with their difference. -/
structure BetaPfExpectationData where
  beta : ℝ
  baseSpectrumDerivative : ℝ
  channelPfExpectation : ℝ
  witness : BetaPfExpectationWitness
  witness_beta : witness.beta = beta
  witness_baseSpectrumDerivative : witness.baseSpectrumDerivative = baseSpectrumDerivative
  witness_channelPfExpectation : witness.channelPfExpectation = channelPfExpectation

/-- Paper-facing proposition: `β` is the audited base-spectrum derivative minus the PF expectation
term.
    prop:beta-pf-expectation -/
theorem paper_gut_beta_pf_expectation (D : BetaPfExpectationData) :
    D.beta = D.baseSpectrumDerivative - D.channelPfExpectation := by
  calc
    D.beta = D.witness.beta := by rw [← D.witness_beta]
    _ = D.witness.baseSpectrumDerivative - D.witness.channelPfExpectation :=
      D.witness.derivativeIdentity
    _ = D.baseSpectrumDerivative - D.channelPfExpectation := by
      rw [D.witness_baseSpectrumDerivative, D.witness_channelPfExpectation]

end Omega.GU
