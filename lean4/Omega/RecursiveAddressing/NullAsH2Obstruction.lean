import Omega.RecursiveAddressing.NullAsLocalSectionObstruction
import Omega.RecursiveAddressing.ObserverIndexedNullStructural

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: a nontrivial Čech-`H²` gluing obstruction excludes global certificate
objects, so the corresponding certificate fiber is empty and the typed readout collapses to
`NULL`.
    prop:null-as-h2-obstruction -/
theorem paper_recursive_addressing_null_as_h2_obstruction
    {State Ref Value Section Piece ι Cech2 : Type} [DecidableEq Value] [Inhabited Piece]
    (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
    (GlobalCert : Ref → Set Section)
    (restrict : ι → Section → Piece)
    (transition : ι → ι → Piece → Piece → Cech2)
    (zero : Cech2)
    (ObstructionVanishes : Ref → Prop)
    {p : State} {r : Ref}
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    (hAdm : r ∈ Adm p)
    (hFiber : (GlobalCert r).Nonempty ↔ (Γ p r).Nonempty)
    (hVisEmpty : Γ p r = ∅ → Vis p r = ∅)
    (hvanish_of_global :
      ∀ {s : Section}, s ∈ GlobalCert r →
        (∀ i j, transition i j (restrict i s) (restrict j s) = zero) →
          ObstructionVanishes r)
    (htransition_trivial :
      ∀ i j {s : Section}, s ∈ GlobalCert r →
        transition i j (restrict i s) (restrict j s) = zero)
    (hH2 : ¬ ObstructionVanishes r) :
    GlobalCert r = ∅ ∧ Γ p r = ∅ ∧ typedReadout Adm Vis p r = Readout.null := by
  have hNoGlobal : ¬ (GlobalCert r).Nonempty := by
    rintro ⟨s, hs⟩
    apply hH2
    exact hvanish_of_global hs (fun i j => htransition_trivial i j hs)
  have hGlobalEmpty : GlobalCert r = ∅ := by
    ext s
    constructor
    · intro hs
      exact False.elim (hNoGlobal ⟨s, hs⟩)
    · intro hs
      cases hs
  have hNoGamma : ¬ (Γ p r).Nonempty := by
    intro hNonempty
    exact hNoGlobal (hFiber.mpr hNonempty)
  have hGammaEmpty : Γ p r = ∅ := by
    ext v
    constructor
    · intro hv
      exact False.elim (hNoGamma ⟨v, hv⟩)
    · intro hv
      cases hv
  have hNonnullCriterion :=
    (paper_null_as_local_section_obstruction
      (State := State) (Ref := Ref) (Value := Value) (Section := Section) (Piece := Piece)
      (ι := ι) Adm Vis Γ hΓ restrict (p := p) (r := r)
      (locals := fun _ => default)).1
  have hNoValue : ¬ ∃ v, typedReadout Adm Vis p r = Readout.value v := by
    intro hvalue
    have hReadable : r ∈ Adm p ∧ Nonempty (PrefixFiber Γ p r) := hNonnullCriterion.mp hvalue
    have hGammaNonempty : (Γ p r).Nonempty :=
      (prefixFiber_nonempty_iff (State := State) (Ref := Ref) (Value := Value) Γ p r).1
        hReadable.2
    exact hNoGamma hGammaNonempty
  have hNull :
      typedReadout Adm Vis p r = Readout.null := by
    exact
      (paper_recursive_addressing_observer_indexed_null_structural
        (State := State) (Ref := Ref) (Value := Value) Adm Vis (p := p) (r := r)).2
        ⟨hAdm, hVisEmpty hGammaEmpty⟩
  exact ⟨hGlobalEmpty, hGammaEmpty, hNull⟩

end Omega.RecursiveAddressing
