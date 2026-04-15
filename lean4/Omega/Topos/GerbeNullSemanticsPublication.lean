import Omega.Topos.GerbeNullSemantics

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the branched-gerbe semantics theorem in
    `2026_conservative_extension_chain_state_forcing_apal`.
    thm:gerbe-null-semantics -/
theorem paper_conservative_extension_gerbe_null_semantics
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
  paper_gluing_failure_gerbe_null_semantics
    Adm CompSec Sec Visible Neutral Obstructed hAdm hComp hSec hDerived

end Omega.Topos
