import Mathlib.Tactic

namespace Omega.RecursiveAddressing.AddressBeforeValue

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a value claim needs both an available address and a nonempty certificate fiber.
    prop:observer-indexed-address-before-value -/
theorem paper_observer_indexed_address_before_value_seeds
    {State Addr Val Cert : Type}
    (A : State → Set Addr) (Γ : State → Addr → Set Cert)
    (ValueAt : State → Addr → Val → Prop)
    (haddr : ∀ {p a v}, ValueAt p a v → a ∈ A p)
    (hcert : ∀ {p a v}, ValueAt p a v → (Γ p a).Nonempty)
    {p : State} {a : Addr} {v : Val}
    (h : a ∉ A p ∨ Γ p a = ∅) :
    ¬ ValueAt p a v := by
  intro hv
  rcases h with h | h
  · exact h (haddr hv)
  · exact (hcert hv).ne_empty h

/-- Wrapper theorem matching the paper-facing package name.
    prop:observer-indexed-address-before-value -/
theorem paper_observer_indexed_address_before_value_package
    {State Addr Val Cert : Type}
    (A : State → Set Addr) (Γ : State → Addr → Set Cert)
    (ValueAt : State → Addr → Val → Prop)
    (haddr : ∀ {p a v}, ValueAt p a v → a ∈ A p)
    (hcert : ∀ {p a v}, ValueAt p a v → (Γ p a).Nonempty)
    {p : State} {a : Addr} {v : Val}
    (h : a ∉ A p ∨ Γ p a = ∅) :
    ¬ ValueAt p a v :=
  paper_observer_indexed_address_before_value_seeds A Γ ValueAt haddr hcert h

end Omega.RecursiveAddressing.AddressBeforeValue
