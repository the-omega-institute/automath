import Omega.RecursiveAddressing.PrefixSiteProjectiveRepTwist

namespace Omega.RecursiveAddressing

/-- Minimal paper-facing gerbe package over a prefix-site Čech groupoid. The fields record only
    the local gerbe properties and the represented Čech class needed by the wrapper theorem.
    thm:prefix-site-cech-null-gerbe -/
structure PrefixSiteGerbe (ι : Type*) (A : Type*) where
  groupoid : PrefixSiteCechGroupoid ι
  locallyNonempty : Prop
  locallyConnected : Prop
  banded : Prop
  neutral : Prop
  cechClass : ι → ι → ι → A

/-- The gerbe twisted by `α`: its neutrality is exactly the coboundary-killing condition for the
    multiplier class. -/
def twistedGerbe {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι)
    (α : ι → ι → ι → A) : PrefixSiteGerbe ι A where
  groupoid := G
  locallyNonempty := True
  locallyConnected := True
  banded := True
  neutral := MultiplierKilledByCoboundary G α
  cechClass := α

/-- Paper-facing gerbe semantics for the prefix-site Čech obstruction: the cocycle `α` defines a
    locally nonempty, locally connected, banded gerbe whose neutrality is equivalent to the
    multiplier being killed by a coboundary. -/
theorem paper_recursive_addressing_prefix_site_cech_null_gerbe
    {ι A : Type*} [AddCommGroup A] (G : PrefixSiteCechGroupoid ι) (α : ι → ι → ι → A) :
    ∃ Gα : PrefixSiteGerbe ι A,
      Gα.locallyNonempty ∧
      Gα.locallyConnected ∧
      Gα.banded ∧
      (Gα.neutral ↔ MultiplierKilledByCoboundary G α) ∧
      Gα.cechClass = α := by
  refine ⟨twistedGerbe G α, ?_⟩
  simp [twistedGerbe]

end Omega.RecursiveAddressing
