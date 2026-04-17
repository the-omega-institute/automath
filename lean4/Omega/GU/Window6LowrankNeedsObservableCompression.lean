import Omega.GU.Window6LieEnvelopeExistenceUniqueness

namespace Omega.GU

open Submodule

/-- Any bracket-closed ambient envelope containing the generators is forced to be top once the
minimal Lie closure is top, so a putative low-rank candidate cannot remain proper.
    prop:window6-lowrank-needs-observable-compression -/
theorem paper_window6_lowrank_needs_observable_compression {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (bracket : V → V → V) (generators h : Submodule K V)
    (hgen : generators ≤ h) (hclosed : Omega.GU.BracketClosed bracket h)
    (hTop : ∀ lieClosure : Submodule K V,
      generators ≤ lieClosure → Omega.GU.BracketClosed bracket lieClosure →
        (∀ W : Submodule K V,
          generators ≤ W → Omega.GU.BracketClosed bracket W → lieClosure ≤ W) →
          lieClosure = ⊤) :
    h = ⊤ := by
  rcases paper_window6_lie_envelope_existence_uniqueness (K := K) (V := V) bracket generators with
    ⟨lieClosure, hlie, _⟩
  have hlie_top : lieClosure = ⊤ := hTop lieClosure hlie.1 hlie.2.1 hlie.2.2
  have htop_le_h : ⊤ ≤ h := by
    rw [← hlie_top]
    exact hlie.2.2 h hgen hclosed
  exact top_le_iff.mp htop_le_h

end Omega.GU
