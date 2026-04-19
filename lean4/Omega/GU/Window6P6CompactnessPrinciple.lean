import Omega.GU.TerminalFoldbin6PushforwardMarkov

namespace Omega.GU

/-- Paper-facing wrapper for the compactness principle attached to the window-`6` pushforward
kernel: the detailed-balance package supplies the selfadjoint input, and the finite-dimensional
commutant then has compact unitary group.
    cor:window6-p6-compactness-principle -/
theorem paper_window6_p6_compactness_principle
    (selfadjoint finiteDim commutantStarAlg unitaryCompact : Prop)
    (hSelfadjoint : selfadjoint)
    (hFinite : finiteDim)
    (hComm : selfadjoint → finiteDim → commutantStarAlg)
    (hCompact : commutantStarAlg → unitaryCompact) :
    selfadjoint ∧ unitaryCompact := by
  let _ := paper_terminal_foldbin6_pushforward_markov
  have hCommutant : commutantStarAlg := hComm hSelfadjoint hFinite
  exact ⟨hSelfadjoint, hCompact hCommutant⟩

end Omega.GU
