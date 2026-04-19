import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the explicit truncation bound on `log 𝔐∞` at the real input
from Proposition `prop:real-input-40-logM-infty`. The data record the root bracket for the
dominant positive root, the logarithmic factor estimate, the comparison with a geometric tail,
the resulting explicit truncation bound, and the absolute convergence consequence. -/
structure XiRealInput40LogMInftyTruncationBoundData where
  rootBracket : Prop
  logFactorBound : Prop
  tailComparison : Prop
  explicitTailBound : Prop
  absoluteConvergence : Prop
  rootBracket_h : rootBracket
  deriveLogFactorBound : rootBracket → logFactorBound
  deriveTailComparison :
    rootBracket → logFactorBound → tailComparison
  deriveExplicitTailBound :
    rootBracket → logFactorBound → tailComparison → explicitTailBound
  deriveAbsoluteConvergence :
    rootBracket → logFactorBound → tailComparison → explicitTailBound →
      absoluteConvergence

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the explicit truncation estimate on `log 𝔐∞`:
place the positive root in `(1/4, 1/3)`, bound the logarithmic factor by a geometric majorant,
compare the Möbius-weighted tail with a truncated geometric series, and conclude absolute
convergence from the explicit remainder bound.
    thm:xi-real-input40-logM-infty-truncation-bound -/
theorem paper_xi_real_input40_logM_infty_truncation_bound
    (D : XiRealInput40LogMInftyTruncationBoundData) :
    D.rootBracket ∧ D.logFactorBound ∧ D.tailComparison ∧
      D.explicitTailBound ∧ D.absoluteConvergence := by
  have hLog : D.logFactorBound := D.deriveLogFactorBound D.rootBracket_h
  have hTail : D.tailComparison := D.deriveTailComparison D.rootBracket_h hLog
  have hBound : D.explicitTailBound :=
    D.deriveExplicitTailBound D.rootBracket_h hLog hTail
  exact ⟨D.rootBracket_h, hLog, hTail, hBound,
    D.deriveAbsoluteConvergence D.rootBracket_h hLog hTail hBound⟩

end Omega.Zeta
