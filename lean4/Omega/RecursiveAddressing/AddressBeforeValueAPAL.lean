import Omega.RecursiveAddressing.FocusedAddressBeforeValue

namespace Omega.RecursiveAddressing.AddressBeforeValueAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the address-before-value proposition.
    prop:address-before-value -/
theorem paper_information_state_address_before_value_apal
    {State Ref Value Cert : Type}
    (Adm : State → Set Ref) (CompSecWitness : State → Ref → Set Cert)
    (ReadAt : State → Ref → Value → Prop)
    (hAdm : ∀ {p r v}, ReadAt p r v → r ∈ Adm p)
    (hComp : ∀ {p r v}, ReadAt p r v → (CompSecWitness p r).Nonempty)
    {p : State} {r : Ref} {v : Value}
    (hRead : ReadAt p r v) :
    r ∈ Adm p ∧ (CompSecWitness p r).Nonempty :=
  Omega.RecursiveAddressing.FocusedAddressBeforeValue.paper_information_state_address_before_value_seeds
    Adm CompSecWitness ReadAt hAdm hComp hRead

end Omega.RecursiveAddressing.AddressBeforeValueAPAL
