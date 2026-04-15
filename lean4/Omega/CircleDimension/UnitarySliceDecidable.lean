import Omega.RecursiveAddressing.NullAsLocalSectionObstruction

namespace Omega.CircleDimension.UnitarySliceDecidable

open Omega.RecursiveAddressing
open FocusedNonNullReadoutCriterion

/-- Finite tagged witness for a `NULL` readout in the unitary-slice wrapper. -/
inductive NullFailureWitness
    {State Ref Value : Type}
    (Adm : State → Set Ref) (Γ : State → Ref → Set Value) (p : State) (r : Ref) : Prop where
  | out : r ∉ Adm p → NullFailureWitness Adm Γ p r
  | cech : Γ p r = ∅ → NullFailureWitness Adm Γ p r
  | hard : False → NullFailureWitness Adm Γ p r

set_option maxHeartbeats 400000 in
/-- Paper-facing package: a non-`NULL` unitary-slice readout carries a finite positive
certificate, a `NULL` readout carries a finite tagged failure witness, and the addressability
predicate is decidable once the admissibility and witness-fiber side conditions are decidable.
    cor:cdim-unitary-slice-decidable -/
theorem paper_cdim_unitary_slice_decidable_package
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    {p : State} {r : Ref}
    [Decidable (r ∈ Adm p)] [Decidable ((Γ p r).Nonempty)] :
    let Addressable : Prop := ∃ v, typedReadout Adm Vis p r = Readout.value v
    let PositiveCertificate :=
      PrefixFiber (State := State) (Ref := Ref) (Value := Value) Γ p r
    (Addressable → Nonempty PositiveCertificate) ∧
      (¬ Addressable → NullFailureWitness Adm Γ p r) ∧
      Nonempty (Decidable Addressable) := by
  dsimp
  have hnonnull :
      (∃ v, typedReadout Adm Vis p r = Readout.value v) ↔
        (r ∈ Adm p ∧ (Γ p r).Nonempty) :=
    (paper_recursive_addressing_observer_indexed_nonnull_criterion
      (State := State) (Ref := Ref) (Value := Value) Adm Vis Γ hΓ (p := p) (r := r)).1
  refine ⟨?_, ?_, ⟨decidable_of_iff (r ∈ Adm p ∧ (Γ p r).Nonempty) hnonnull.symm⟩⟩
  · intro hAddressable
    exact
      (prefixFiber_nonempty_iff (State := State) (Ref := Ref) (Value := Value) Γ p r).2
        (hnonnull.mp hAddressable).2
  · intro hNotAddressable
    by_cases hAdm : r ∈ Adm p
    · have hΓnot : ¬ (Γ p r).Nonempty := by
        intro hΓnonempty
        apply hNotAddressable
        exact hnonnull.mpr ⟨hAdm, hΓnonempty⟩
      have hΓempty : Γ p r = ∅ := by
        ext v
        constructor
        · intro hv
          exact False.elim (hΓnot ⟨v, hv⟩)
        · intro hv
          cases hv
      exact NullFailureWitness.cech hΓempty
    · exact NullFailureWitness.out hAdm

/-- Paper label wrapper for the unitary-slice decidability corollary. -/
def paper_cdim_unitary_slice_decidable : Prop := by
  exact
    ∀ {State Ref Value : Type} [DecidableEq Value]
      (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
      (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
      {p : State} {r : Ref}
      [Decidable (r ∈ Adm p)] [Decidable ((Γ p r).Nonempty)],
      let Addressable : Prop := ∃ v, typedReadout Adm Vis p r = Readout.value v
      let PositiveCertificate :=
        PrefixFiber (State := State) (Ref := Ref) (Value := Value) Γ p r
      (Addressable → Nonempty PositiveCertificate) ∧
        (¬ Addressable → NullFailureWitness Adm Γ p r) ∧
        Nonempty (Decidable Addressable)

end Omega.CircleDimension.UnitarySliceDecidable
