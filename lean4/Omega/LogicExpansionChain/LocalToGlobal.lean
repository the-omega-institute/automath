import Mathlib.Tactic

namespace Omega.LogicExpansionChain

/-- A witness for a compatible local family over some cover of an object.
    The compatibility datum is kept abstract because the local-to-global wrapper only needs the
    existence of such a witness, not its internal shape.
    prop:logic-expansion-local-to-global -/
structure CompatibleLocalFamily (Obj Section : Type*) where
  target : Obj
  ι : Type
  cover : ι → Obj
  localSec : ι → Section
  compatible : Prop

/-- `CompSec` means that at the target object `address p r` there exists a witness cover together
    with a compatible local family of sections on that cover.
    prop:logic-expansion-local-to-global -/
def CompSec
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    (p : State) (r : Ref) : Prop :=
  ∃ W : CompatibleLocalFamily Obj Section,
    W.target = address p r ∧
      W.compatible ∧ ∀ i, W.localSec i ∈ F (W.cover i)

/-- `Sec` is the existence of a global section at the target object `address p r`.
    prop:logic-expansion-local-to-global -/
def Sec
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    (p : State) (r : Ref) : Prop :=
  (F (address p r)).Nonempty

set_option maxHeartbeats 400000 in
/-- Paper-facing local-to-global principle: a witness of `CompSec` is a cover together with a
    compatible local family, so an assumed gluing rule at `a = [r]_p` immediately yields a global
    section, i.e. `Sec`.
    prop:logic-expansion-local-to-global -/
theorem paper_logic_expansion_local_to_global
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    (glue :
      ∀ W : CompatibleLocalFamily Obj Section,
        W.compatible →
        (∀ i, W.localSec i ∈ F (W.cover i)) →
        ∃ σ, σ ∈ F W.target)
    {p : State} {r : Ref}
    (hComp : CompSec address F p r) :
    Sec address F p r := by
  rcases hComp with ⟨W, htarget, hWcompat, hWlocal⟩
  rcases glue W hWcompat hWlocal with ⟨σ, hσ⟩
  exact ⟨σ, by simpa [Sec, htarget] using hσ⟩

end Omega.LogicExpansionChain
