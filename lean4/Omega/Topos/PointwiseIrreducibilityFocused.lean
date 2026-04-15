import Omega.Topos.PointwiseIrreducibility

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the irreducibility of gluing predicates in
    `2026_conservative_extension_chain_state_forcing_apal_focused`.
    thm:pointwise-irreducibility -/
theorem paper_conservative_extension_pointwise_irreducibility_focused
    {Ref : Type}
    (Adm LocSec CompSec Sec : Ref → Prop)
    (LowerEq : Ref → Ref → Prop)
    (r1 r2 r3 r4 : Ref)
    (h12 : LowerEq r1 r2)
    (h13 : LowerEq r1 r3)
    (h14 : LowerEq r1 r4)
    (hAdm1 : Adm r1)
    (hAdm2 : Adm r2)
    (hAdm3 : Adm r3)
    (hAdm4 : Adm r4)
    (hr1 : CompSec r1 ∧ Sec r1)
    (hr2 : CompSec r2 ∧ ¬ Sec r2)
    (hr3 : LocSec r3 ∧ ¬ CompSec r3)
    (hr4 : CompSec r4 ∧ Sec r4) :
    ¬ LowerDefinable LowerEq CompSec ∧
      ¬ LowerDefinable LowerEq Sec ∧
      ¬ LowerDefinable LowerEq (NullGlue Adm CompSec Sec) :=
  paper_gluing_failure_pointwise_irreducibility
    Adm LocSec CompSec Sec LowerEq r1 r2 r3 r4 h12 h13 h14 hAdm1 hAdm2 hAdm3 hAdm4 hr1 hr2
    hr3 hr4

end Omega.Topos
