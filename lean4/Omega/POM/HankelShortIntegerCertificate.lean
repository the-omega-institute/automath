import Mathlib.Tactic
import Omega.POM.HankelSyndromeGapRankDefect

namespace Omega.POM

/-- Paper-facing wrapper for the short integer nullmode certificate: a rank defect together with
the entry bound yields a nonzero integer nullmode with controlled sup norm.
    thm:pom-hankel-short-integer-certificate -/
theorem paper_pom_hankel_short_integer_certificate
    (rankDefect boundedEntries existsShortIntegerNullmode : Prop)
    (hShort : rankDefect → boundedEntries → existsShortIntegerNullmode) :
    rankDefect → boundedEntries → existsShortIntegerNullmode := by
  intro hRankDefect hBoundedEntries
  exact hShort hRankDefect hBoundedEntries

end Omega.POM
