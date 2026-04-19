import Omega.GU.TerminalFoldbin6PushforwardMarkov

namespace Omega.GU

/-- Paper-facing wrapper for the audited window-`6` pushforward characteristic-polynomial
certificate: the nontrivial factorization is recorded together with its degree, irreducibility,
squarefreeness, and full symmetric Galois group.
    thm:terminal-window6-pushforward-charpoly-galois -/
theorem paper_terminal_window6_pushforward_charpoly_galois
    (charpolyFactorization q6Degree20 q6Irreducible q6Squarefree q6GaloisS20 : Prop)
    (hFactor : charpolyFactorization)
    (hDeg : q6Degree20)
    (hIrred : q6Irreducible)
    (hSqfree : q6Squarefree)
    (hGal : q6GaloisS20) :
    charpolyFactorization ∧ q6Degree20 ∧ q6Irreducible ∧ q6Squarefree ∧ q6GaloisS20 := by
  exact ⟨hFactor, hDeg, hIrred, hSqfree, hGal⟩

end Omega.GU
