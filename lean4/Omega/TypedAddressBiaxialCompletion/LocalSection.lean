import Mathlib.Tactic
import Omega.Topos.LocalSectionCriterion

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing typed-address specialization of the local-section criterion.
    prop:typed-address-biaxial-completion-local-section -/
theorem paper_typed_address_biaxial_completion_local_section
    {Addr Cert : Type} (read : Addr → Option Cert) (F : Addr → Set Cert)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty) (a : Addr) :
    (read a ≠ none ↔ (F a).Nonempty) ∧
      (read a = none ↔ F a = ∅) := by
  have hnonnull :
      read a ≠ none ↔ (F a).Nonempty :=
    Omega.Topos.LocalSectionCriterion.paper_typed_address_biaxial_completion_local_section_package
      read F hcompat a
  have hnull :
      read a = none ↔ F a = ∅ := by
    calc
      read a = none ↔ ¬ read a ≠ none := by simp
      _ ↔ ¬ (F a).Nonempty := not_congr hnonnull
      _ ↔ F a = ∅ := Set.not_nonempty_iff_eq_empty
  exact ⟨hnonnull, hnull⟩

end Omega.TypedAddressBiaxialCompletion
