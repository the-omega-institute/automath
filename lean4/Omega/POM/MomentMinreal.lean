import Mathlib.Tactic
import Omega.POM.DeltaMinExtraReadouts
import Omega.POM.MomentResonance

namespace Omega.POM

/-- Chapter-local audited data for the moment/Hankel minimal-realization corollary. The lower
bound packages the Hankel witness, the upper bound packages the companion realization, and the
last field records the generic identification between Hankel rank and minimal realization
dimension used to close the equality chain. -/
structure MomentMinrealData where
  hankelRank : ℕ
  recurrenceOrder : ℕ
  minimalRealizationDim : ℕ
  hankelLowerBound : recurrenceOrder ≤ hankelRank
  companionUpperBound : hankelRank ≤ recurrenceOrder
  hankelRank_eq_minimalRealizationDim : hankelRank = minimalRealizationDim

/-- Paper-facing wrapper for the audited moment-minimal-realization package: once the Hankel
certificate gives the lower bound, the companion realization gives the matching upper bound, and
minimal realization dimension is identified with Hankel rank, all three quantities coincide.
    cor:pom-moment-minreal -/
theorem paper_pom_moment_minreal (D : MomentMinrealData) :
    D.hankelRank = D.recurrenceOrder ∧ D.minimalRealizationDim = D.recurrenceOrder := by
  have hrank : D.hankelRank = D.recurrenceOrder :=
    le_antisymm D.companionUpperBound D.hankelLowerBound
  refine ⟨hrank, ?_⟩
  calc
    D.minimalRealizationDim = D.hankelRank := D.hankelRank_eq_minimalRealizationDim.symm
    _ = D.recurrenceOrder := hrank

end Omega.POM
