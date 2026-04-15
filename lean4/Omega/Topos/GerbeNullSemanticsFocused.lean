import Omega.Topos.GerbeNullSemanticsPublication

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the branched-gerbe semantics theorem.
    thm:gerbe-null-semantics -/
theorem paper_conservative_extension_gerbe_null_semantics_focused
    {Ref Branch : Type}
    (Adm CompSec Sec : Ref → Prop)
    (Visible : Ref → Set Branch)
    (Neutral Obstructed : Ref → Branch → Prop)
    {r : Ref}
    (hAdm : Adm r)
    (hComp : CompSec r ↔ Set.Nonempty (Visible r))
    (hSec : Sec r ↔ ∃ v, v ∈ Visible r ∧ Neutral r v)
    (hDerived :
      ∀ v, v ∈ Visible r → (¬ Neutral r v ↔ Obstructed r v)) :
    (CompSec r ↔ Set.Nonempty (Visible r)) ∧
      (Sec r ↔ ∃ v, v ∈ Visible r ∧ Neutral r v) ∧
      (NullGlue Adm CompSec Sec r ↔
        Set.Nonempty (Visible r) ∧
          ∀ v, v ∈ Visible r → ¬ Neutral r v) ∧
      (NullGlue Adm CompSec Sec r ↔
        Set.Nonempty (Visible r) ∧
          ∀ v, v ∈ Visible r → Obstructed r v) :=
  paper_conservative_extension_gerbe_null_semantics
    Adm CompSec Sec Visible Neutral Obstructed hAdm hComp hSec hDerived

end Omega.Topos
