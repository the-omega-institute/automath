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

/-- Logic-expansion wrapper: each chapter-local null mode forces ambient nullness by
specializing the generic topos implications at the current state.
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
  constructor
  · intro hLoc
    exact Omega.Topos.nullLoc_implies_null (Adm p) (LocSec p) (Sec p) r
      (fun {x} hx => hcompLoc (hsecComp hx)) hLoc
  constructor
  · intro hCmp
    exact Omega.Topos.nullCmp_implies_null (Adm p) (LocSec p) (CompSec p) (Sec p) r
      (fun {x} hx => hsecComp hx) hCmp
  · intro hGlue
    exact Omega.Topos.nullGlue_implies_null (Adm p) (CompSec p) (Sec p) r hGlue

end Omega.LogicExpansionChain
