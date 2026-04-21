import Mathlib.Data.ZMod.Basic
import Omega.Folding.ModSemiringsAnnihilatorValuationLattice
import Omega.Folding.ModSemiringsSquarefreeNilpotentBranch
import Omega.Folding.Window6

namespace Omega

/-- The idempotent locus in `ZMod 21`, matching the `m = 6` CRT skeleton. -/
def window6Idempotents : Finset (ZMod 21) :=
  Finset.univ.filter fun x => x ^ 2 = x

/-- The nilradical of `ZMod 21`, written as the finite search for nilpotent residue classes. -/
def window6Nilradical : Finset (ZMod 21) :=
  Finset.univ.filter fun x => ∃ n ∈ Finset.range 22, 0 < n ∧ x ^ n = 0

lemma window6Idempotents_eq :
    window6Idempotents = ({0, 1, 7, 15} : Finset (ZMod 21)) := by
  ext x
  simpa [window6Idempotents] using (zmod21_idempotents_complete x)

lemma window6Nilradical_eq :
    window6Nilradical = ({0} : Finset (ZMod 21)) := by
  native_decide

/-- Paper label: `prop:fold-mod-semirings-window6-semisimple-skeleton`. -/
theorem paper_fold_mod_semirings_window6_semisimple_skeleton :
    window6Idempotents = ({0, 1, 7, 15} : Finset (ZMod 21)) ∧
      Fintype.card (Units (ZMod 21)) = 12 ∧
      window6Nilradical = ({0} : Finset (ZMod 21)) := by
  refine ⟨window6Idempotents_eq, ?_, window6Nilradical_eq⟩
  native_decide

end Omega
