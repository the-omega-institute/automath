import Omega.GU.Window6LieEnvelopeClosure

namespace Omega.GU

open Submodule

theorem paper_window6_lie_envelope_existence_uniqueness {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (bracket : V → V → V) (generators : Submodule K V) :
    ∃! lieClosure : Submodule K V,
      generators ≤ lieClosure ∧
        BracketClosed bracket lieClosure ∧
        ∀ W : Submodule K V,
          generators ≤ W → BracketClosed bracket W → lieClosure ≤ W := by
  classical
  let candidates : Set (Submodule K V) :=
    {W | generators ≤ W ∧ BracketClosed bracket W}
  let lieClosure : Submodule K V := sInf candidates
  have hlie :
      generators ≤ lieClosure ∧
        BracketClosed bracket lieClosure ∧
        ∀ W : Submodule K V,
          generators ≤ W → BracketClosed bracket W → lieClosure ≤ W := by
    refine ⟨?_, ?_, ?_⟩
    · exact le_sInf fun W hW => hW.1
    · intro x y hx hy
      rw [Submodule.mem_sInf]
      intro W hW
      exact hW.2 ((sInf_le hW) hx) ((sInf_le hW) hy)
    · intro W hgen hclosed
      exact sInf_le ⟨hgen, hclosed⟩
  refine ⟨lieClosure, hlie, ?_⟩
  intro W hW
  exact le_antisymm (hW.2.2 lieClosure hlie.1 hlie.2.1) (hlie.2.2 W hW.1 hW.2.1)

end Omega.GU
