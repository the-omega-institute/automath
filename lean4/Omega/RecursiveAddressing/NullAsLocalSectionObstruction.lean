import Omega.RecursiveAddressing.ObserverIndexedReadoutForcingCriterion
import Omega.RecursiveAddressing.ReadoutSeparatednessNull

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

/-- The prefix-site fiber over `(p, r)` packaged as a subtype of admissible local witnesses. -/
abbrev PrefixFiber
    {State Ref Value : Type}
    (Γ : State → Ref → Set Value) (p : State) (r : Ref) :=
  {v : Value // v ∈ Γ p r}

theorem prefixFiber_nonempty_iff
    {State Ref Value : Type}
    (Γ : State → Ref → Set Value) (p : State) (r : Ref) :
    Nonempty (PrefixFiber (State := State) (Ref := Ref) (Value := Value) Γ p r) ↔
      (Γ p r).Nonempty := by
  constructor
  · rintro ⟨⟨v, hv⟩⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing chapter wrapper: a typed readout is non-`NULL` exactly when the prefix-site fiber
over the address is nonempty, and any compatible finite family of local sections glues uniquely as
soon as restriction to all cover pieces is separated by its tuple of finite restrictions.
    prop:null-as-local-section-obstruction -/
theorem paper_null_as_local_section_obstruction
    {State Ref Value Section Piece ι : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    (restrict : ι → Section → Piece)
    {p : State} {r : Ref} (locals : ι → Piece) :
    (((∃ v, typedReadout (State := State) (Ref := Ref) (Value := Value) Adm Vis p r =
          Readout.value v) ↔
        (r ∈ Adm p ∧
          Nonempty (PrefixFiber (State := State) (Ref := Ref) (Value := Value) Γ p r))) ∧
      ((∃ s : Section, ∀ i : ι, restrict i s = locals i) →
        Function.Injective (fun s : Section => fun i : ι => restrict i s) →
        ∃! s : Section, ∀ i : ι, restrict i s = locals i)) := by
  constructor
  · have hnonnull :
        (∃ v, typedReadout (State := State) (Ref := Ref) (Value := Value) Adm Vis p r =
            Readout.value v) ↔
          (r ∈ Adm p ∧ (Γ p r).Nonempty) :=
      (paper_recursive_addressing_observer_indexed_nonnull_criterion
        Adm Vis Γ hΓ (p := p) (r := r)).1
    exact hnonnull.trans <| by
      constructor
      · rintro ⟨hAdm, hNonempty⟩
        exact ⟨hAdm, (prefixFiber_nonempty_iff (State := State) (Ref := Ref)
          (Value := Value) Γ p r).2 hNonempty⟩
      · rintro ⟨hAdm, hNonempty⟩
        exact ⟨hAdm, (prefixFiber_nonempty_iff (State := State) (Ref := Ref)
          (Value := Value) Γ p r).1 hNonempty⟩
  · intro hGlue hinj
    rcases hGlue with ⟨s₀, hs₀⟩
    refine ⟨s₀, hs₀, ?_⟩
    intro t ht
    have hsep :
        ∀ s t : Section, (∀ i : ι, restrict i s = restrict i t) → s = t :=
      (paper_recursive_addressing_readout_separatedness_null restrict).2 hinj
    exact hsep t s₀ (fun i => (ht i).trans (hs₀ i).symm)

/-- Paper-facing obstruction readout: a nontrivial H2 gluing obstruction rules out any
nonempty prefix fiber, so the fiber is empty and the existing NULL readout criterion fires.
    prop:null-as-h2-obstruction -/
theorem paper_null_as_h2_obstruction
    {Addr Obj : Type}
    (Fiber : Addr → Set Obj) (NullReadout Obstructed : Addr → Prop)
    (htrivial : ∀ {a : Addr}, (Fiber a).Nonempty → ¬ Obstructed a)
    (hnull : ∀ {a : Addr}, Fiber a = (∅ : Set Obj) → NullReadout a) :
    ∀ a : Addr, Obstructed a → Fiber a = (∅ : Set Obj) ∧ NullReadout a := by
  intro a hObs
  have hEmpty : Fiber a = (∅ : Set Obj) := by
    ext x
    constructor
    · intro hx
      exact False.elim ((htrivial (a := a) ⟨x, hx⟩) hObs)
    · intro hx
      cases hx
  exact ⟨hEmpty, hnull hEmpty⟩

end Omega.RecursiveAddressing
