import Omega.GU.StrongLumpabilitySpectralFalsifier
import Omega.GU.TerminalFoldbin6PushforwardMarkov
import Omega.GU.Window6MinimalMarkovObstructionPureF8Tail

namespace Omega.GU

/-- Publication-facing corollary packaging the minimal-memory Markov closure for the terminal
window-6 foldbin quotient together with its audited spectral-gap and TV-mixing consequences.
    cor:terminal-foldbin6-minimal-markov-closure-gap -/
theorem paper_terminal_foldbin6_minimal_markov_closure_gap
    (pushforwardMarkov strongLumpabilityFailure minimalMarkovClosure spectralGapBound
      tvExponentialMixing : Prop)
    (hPush : pushforwardMarkov) (hFail : strongLumpabilityFailure)
    (hClosure : pushforwardMarkov -> strongLumpabilityFailure -> minimalMarkovClosure)
    (hGap : minimalMarkovClosure -> spectralGapBound)
    (hMix : spectralGapBound -> tvExponentialMixing) :
    minimalMarkovClosure ∧ spectralGapBound ∧ tvExponentialMixing := by
  have hMinimal : minimalMarkovClosure := hClosure hPush hFail
  have hSpectral : spectralGapBound := hGap hMinimal
  exact ⟨hMinimal, hSpectral, hMix hSpectral⟩

end Omega.GU
