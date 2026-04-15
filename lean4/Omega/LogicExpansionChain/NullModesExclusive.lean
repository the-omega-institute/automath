import Omega.Topos.NullTrichotomy

namespace Omega.LogicExpansionChain

theorem paper_logic_expansion_null_modes_exclusive
    {State Ref : Type}
    (Adm LocSec CompSec Sec : State → Ref → Prop)
    {p : State} (r : Ref)
    (hcompLoc : ∀ {s : State} {x : Ref}, CompSec s x → LocSec s x) :
    (Omega.Topos.NullLoc (Adm p) (LocSec p) r → ¬ Omega.Topos.NullCmp (Adm p) (LocSec p) (CompSec p) r) ∧
      (Omega.Topos.NullLoc (Adm p) (LocSec p) r → ¬ Omega.Topos.NullGlue (Adm p) (CompSec p) (Sec p) r) ∧
      (Omega.Topos.NullCmp (Adm p) (LocSec p) (CompSec p) r → ¬ Omega.Topos.NullGlue (Adm p) (CompSec p) (Sec p) r) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Omega.Topos.nullLoc_not_nullCmp (Adm p) (LocSec p) (CompSec p) r
  · exact Omega.Topos.nullLoc_not_nullGlue
      (Adm p) (LocSec p) (CompSec p) (Sec p) r
      (fun {x} hx => hcompLoc (s := p) (x := x) hx)
  · exact Omega.Topos.nullCmp_not_nullGlue (Adm p) (LocSec p) (CompSec p) (Sec p) r

end Omega.LogicExpansionChain
