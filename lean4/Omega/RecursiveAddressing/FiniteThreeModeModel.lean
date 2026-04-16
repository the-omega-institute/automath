import Omega.Topos.NullTrichotomy

namespace Omega.RecursiveAddressing

inductive AbsenceRef where
  | loc
  | cmp
  | glue
  deriving DecidableEq, Repr

def Adm : AbsenceRef → Prop := fun _ => True

def LocSec : AbsenceRef → Prop
  | .loc => False
  | .cmp => True
  | .glue => True

def CompSec : AbsenceRef → Prop
  | .loc => False
  | .cmp => False
  | .glue => True

def Sec : AbsenceRef → Prop := fun _ => False

/-- A concrete finite witness exhibiting the three structural absence modes. -/
theorem paper_finite_three_mode_model_seeds :
    ∃ rLoc rCmp rGlue : AbsenceRef,
      Omega.Topos.NullLoc Adm LocSec rLoc ∧
      Omega.Topos.NullCmp Adm LocSec CompSec rCmp ∧
      Omega.Topos.NullGlue Adm CompSec Sec rGlue := by
  refine ⟨.loc, .cmp, .glue, ?_, ?_, ?_⟩ <;>
    simp [Omega.Topos.NullLoc, Omega.Topos.NullCmp, Omega.Topos.NullGlue, Adm, LocSec,
      CompSec, Sec]

end Omega.RecursiveAddressing
