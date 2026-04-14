import Omega.Topos.NullClassificationUnderRefinement

namespace Omega.Topos.NullClassificationUnderRefinementAPAL

open Omega.Topos

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the refinement classification theorem.
    thm:null-classification-under-refinement -/
theorem paper_conservative_extension_null_classification_under_refinement_apal
    {State Ref : Type}
    (Adm LocSec CompSec Sec : State → Ref → Prop)
    {p q : State} (r : Ref)
    [Decidable (LocSec q r)] [Decidable (CompSec q r)]
    (hpersist : Null (Adm p) (Sec p) r → Null (Adm q) (Sec q) r)
    (hnull : Null (Adm p) (Sec p) r)
    (hcompLoc : ∀ {s : State} {x : Ref}, CompSec s x → LocSec s x)
    (hsecComp : ∀ {s : State} {x : Ref}, Sec s x → CompSec s x) :
    ExactlyOne3
      (NullLoc (Adm q) (LocSec q) r)
      (NullCmp (Adm q) (LocSec q) (CompSec q) r)
      (NullGlue (Adm q) (CompSec q) (Sec q) r) :=
  paper_conservative_extension_null_classification_under_refinement_seeds
    Adm LocSec CompSec Sec r hpersist hnull hcompLoc hsecComp

end Omega.Topos.NullClassificationUnderRefinementAPAL
