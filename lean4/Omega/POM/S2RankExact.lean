import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-s2-rank-exact`. The lower and upper rank certificates force the Hankel
rank to be exactly `3`, and the minimal realization dimension matches that rank. -/
theorem paper_pom_s2_rank_exact (rankH minDim : ℕ) (hLower : 3 ≤ rankH) (hUpper : rankH ≤ 3)
    (hMin : minDim = rankH) : rankH = 3 ∧ minDim = 3 := by
  have hrank : rankH = 3 := by omega
  constructor
  · exact hrank
  · omega

end Omega.POM
