import Omega.Topos.NullTrichotomy

namespace Omega.Topos

/-- A predicate is lower-layer definable when it is constant on lower-layer
    indistinguishability classes. -/
def LowerDefinable {Ref : Type*} (LowerEq : Ref → Ref → Prop) (P : Ref → Prop) : Prop :=
  ∀ ⦃r s : Ref⦄, LowerEq r s → (P r ↔ P s)

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the irreducibility of gluing predicates with
    respect to lower-layer indistinguishability.
    thm:pointwise-irreducibility -/
theorem paper_gluing_failure_pointwise_irreducibility
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
      ¬ LowerDefinable LowerEq (NullGlue Adm CompSec Sec) := by
  let _ := h14
  let _ := hAdm1
  let _ := hAdm3
  let _ := hAdm4
  let _ := hr4
  refine ⟨?_, ?_, ?_⟩
  · intro hdef
    have hcomp : CompSec r1 ↔ CompSec r3 := hdef h13
    exact hr3.2 (hcomp.mp hr1.1)
  · intro hdef
    have hsec : Sec r1 ↔ Sec r2 := hdef h12
    exact hr2.2 (hsec.mp hr1.2)
  · intro hdef
    have hglue : NullGlue Adm CompSec Sec r1 ↔ NullGlue Adm CompSec Sec r2 := hdef h12
    have hNull2 : NullGlue Adm CompSec Sec r2 := ⟨hAdm2, hr2.1, hr2.2⟩
    have hNotNull1 : ¬ NullGlue Adm CompSec Sec r1 := by
      intro hNull1
      exact hNull1.2.2 hr1.2
    exact hNotNull1 (hglue.mpr hNull2)

end Omega.Topos
