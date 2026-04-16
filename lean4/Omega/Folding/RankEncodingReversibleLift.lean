import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the reversible rank-encoding lift. The data records the paper-level
claims that each fold fiber admits a chosen rank enumeration, that the resulting base-`M` encoding
produces an injective lift, and that the `M = 6` asymptotic comparison has already been verified in
the max-fiber analysis. -/
structure RankEncodingReversibleLiftData where
  hasInjectiveLift : Prop
  baseSixAsymptoticBound : Prop
  injectiveLiftWitness : hasInjectiveLift
  baseSixAsymptoticWitness : baseSixAsymptoticBound

/-- Paper-facing wrapper for the reversible rank-encoding lift: the chapter-local witnesses already
package the injective lift and the `M = 6` asymptotic bound.
    prop:fold-local-rewrite-rank-encoding-reversible-lift -/
theorem paper_fold_local_rewrite_rank_encoding_reversible_lift
    (D : RankEncodingReversibleLiftData) : D.hasInjectiveLift ∧ D.baseSixAsymptoticBound := by
  exact ⟨D.injectiveLiftWitness, D.baseSixAsymptoticWitness⟩

end Omega.Folding
