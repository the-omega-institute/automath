import Mathlib.Tactic

namespace Omega.Discussion

/-- Pointwise eventual stabilization determines a unique limit coefficient sequence: for each
index, choose a stable tail value and then compare any two candidates on a common tail.
    thm:discussion-cmv-stabilization-core -/
theorem paper_discussion_cmv_stabilization_core {α : Type} (aL : Nat → Nat → α)
    (hstab : ∀ n, ∃ N, ∀ L ≥ N, aL L n = aL N n) :
    ∃! aInf : Nat → α, ∀ n, ∃ N, ∀ L ≥ N, aL L n = aInf n := by
  classical
  let N0 : Nat → Nat := fun n => Classical.choose (hstab n)
  let aInf : Nat → α := fun n => aL (N0 n) n
  have htail : ∀ n, ∀ L ≥ N0 n, aL L n = aInf n := by
    intro n L hL
    simpa [N0, aInf] using (Classical.choose_spec (hstab n)) L hL
  refine ⟨aInf, ?_, ?_⟩
  · intro n
    exact ⟨N0 n, fun L hL => htail n L hL⟩
  · intro b hb
    funext n
    rcases hb n with ⟨Nb, hNb⟩
    let M := max (N0 n) Nb
    have hMInf : aL M n = aInf n := htail n M (le_max_left _ _)
    have hMb : aL M n = b n := hNb M (le_max_right _ _)
    exact hMb.symm.trans hMInf

end Omega.Discussion
