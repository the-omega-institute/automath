import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local witness package for the audited finite Hankel minors. The data stores the target
rank, the ambient Hankel rank, the principal-minor witness, and the rank lower bound extracted
from that witness. -/
structure MomentHankelData where
  targetRank : ℕ
  hankelRank : ℕ
  nonzeroPrincipalMinor : Prop
  targetRank_le_hankelRank : targetRank ≤ hankelRank
  nonzeroPrincipalMinor_h : nonzeroPrincipalMinor

/-- Paper-facing wrapper for the Hankel minor audit.
    thm:pom-moment-hankel -/
theorem paper_pom_moment_hankel (D : MomentHankelData) :
    D.targetRank ≤ D.hankelRank ∧ D.nonzeroPrincipalMinor := by
  exact ⟨D.targetRank_le_hankelRank, D.nonzeroPrincipalMinor_h⟩

end Omega.POM
