import Omega.Topos.NullTrichotomy

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Logic-expansion wrapper: each constructive `NULL` mode already contains enough data to force
abstract nullness at the current state/reference.
    prop:logic-expansion-null-modes-imply-null -/
theorem paper_logic_expansion_null_modes_imply_null
    {State Ref : Type}
    (Adm LocSec CompSec Sec : State → Ref → Prop)
    {p : State} (r : Ref)
    (hcompLoc : ∀ {s : State} {x : Ref}, CompSec s x → LocSec s x)
    (hsecComp : ∀ {s : State} {x : Ref}, Sec s x → CompSec s x) :
    (Omega.Topos.NullLoc (Adm p) (LocSec p) r → Omega.Topos.Null (Adm p) (Sec p) r) ∧
      (Omega.Topos.NullCmp (Adm p) (LocSec p) (CompSec p) r →
        Omega.Topos.Null (Adm p) (Sec p) r) ∧
      (Omega.Topos.NullGlue (Adm p) (CompSec p) (Sec p) r →
        Omega.Topos.Null (Adm p) (Sec p) r) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Omega.Topos.nullLoc_implies_null (Adm p) (LocSec p) (Sec p) r
      (fun {x} hx => hcompLoc (hsecComp hx))
  · exact Omega.Topos.nullCmp_implies_null (Adm p) (LocSec p) (CompSec p) (Sec p) r
      (fun {x} hx => hsecComp hx)
  · exact Omega.Topos.nullGlue_implies_null (Adm p) (CompSec p) (Sec p) r

end Omega.LogicExpansionChain
