import Omega.RecursiveAddressing.AddressBeforeValue

namespace Omega.RecursiveAddressing.FocusedAddressBeforeValue

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: any non-null readout carries both admissibility and a compatible-section
    witness.
    prop:address-before-value -/
theorem paper_information_state_address_before_value_seeds
    {State Ref Value Cert : Type}
    (Adm : State → Set Ref) (CompSecWitness : State → Ref → Set Cert)
    (ReadAt : State → Ref → Value → Prop)
    (hAdm : ∀ {p r v}, ReadAt p r v → r ∈ Adm p)
    (hComp : ∀ {p r v}, ReadAt p r v → (CompSecWitness p r).Nonempty)
    {p : State} {r : Ref} {v : Value}
    (hRead : ReadAt p r v) :
    r ∈ Adm p ∧ (CompSecWitness p r).Nonempty := by
  exact ⟨hAdm hRead, hComp hRead⟩

/-- Wrapper theorem matching the focused-publication label.
    prop:address-before-value -/
theorem paper_information_state_address_before_value_package
    {State Ref Value Cert : Type}
    (Adm : State → Set Ref) (CompSecWitness : State → Ref → Set Cert)
    (ReadAt : State → Ref → Value → Prop)
    (hAdm : ∀ {p r v}, ReadAt p r v → r ∈ Adm p)
    (hComp : ∀ {p r v}, ReadAt p r v → (CompSecWitness p r).Nonempty)
    {p : State} {r : Ref} {v : Value}
    (hRead : ReadAt p r v) :
    r ∈ Adm p ∧ (CompSecWitness p r).Nonempty :=
  paper_information_state_address_before_value_seeds Adm CompSecWitness ReadAt hAdm hComp hRead

end Omega.RecursiveAddressing.FocusedAddressBeforeValue
