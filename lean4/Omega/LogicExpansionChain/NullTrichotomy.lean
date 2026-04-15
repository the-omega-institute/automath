import Omega.Topos.NullTrichotomy

namespace Omega.LogicExpansionChain

open Omega.Topos

set_option maxHeartbeats 400000 in
/-- Logic-expansion wrapper: once the local-section and compatibility predicates are
decidable at the current state, nullness splits constructively into the three standard
failure modes.
    prop:logic-expansion-null-trichotomy -/
theorem paper_logic_expansion_null_trichotomy
    {State Ref : Type}
    (Adm LocSec CompSec Sec : State → Ref → Prop)
    {p : State} (r : Ref)
    [Decidable (LocSec p r)] [Decidable (CompSec p r)]
    (hcompLoc : ∀ {s : State} {x : Ref}, CompSec s x → LocSec s x)
    (hsecComp : ∀ {s : State} {x : Ref}, Sec s x → CompSec s x) :
    Omega.Topos.Null (Adm p) (Sec p) r ↔
      Omega.Topos.ExactlyOne3
        (Omega.Topos.NullLoc (Adm p) (LocSec p) r)
        (Omega.Topos.NullCmp (Adm p) (LocSec p) (CompSec p) r)
        (Omega.Topos.NullGlue (Adm p) (CompSec p) (Sec p) r) :=
  Omega.Topos.paper_null_trichotomy_seeds
    (Adm p) (LocSec p) (CompSec p) (Sec p) r
    (fun {_} hx => hcompLoc hx)
    (fun {_} hx => hsecComp hx)

end Omega.LogicExpansionChain
