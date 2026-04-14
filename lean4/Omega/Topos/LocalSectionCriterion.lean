import Mathlib.Tactic

/-!
# Local section criterion seeds

This file registers the paper-facing seed/package wrapper for
`prop:typed-address-biaxial-completion-local-section`.
-/

namespace Omega.Topos.LocalSectionCriterion

/-- Paper seed for the local-section criterion.
    A readable address is equivalent to the nonemptiness of its certificate fiber.
    prop:typed-address-biaxial-completion-local-section -/
theorem paper_typed_address_biaxial_completion_local_section_seeds
    {Addr Cert : Type} (read : Addr → Option Cert) (F : Addr → Set Cert)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty) (a : Addr) :
    read a ≠ none ↔ (F a).Nonempty := by
  rw [← Option.isSome_iff_ne_none]
  exact hcompat a

/-- Packaged form of the local-section criterion seeds.
    prop:typed-address-biaxial-completion-local-section -/
theorem paper_typed_address_biaxial_completion_local_section_package
    {Addr Cert : Type} (read : Addr → Option Cert) (F : Addr → Set Cert)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty) (a : Addr) :
    read a ≠ none ↔ (F a).Nonempty :=
  paper_typed_address_biaxial_completion_local_section_seeds read F hcompat a

end Omega.Topos.LocalSectionCriterion
