import Mathlib.Tactic
import Omega.RecursiveAddressing.ReadoutSeparatednessNull
import Omega.Topos.LocalSectionCriterion

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper for the typed-address readability criterion: non-`NULL` is exactly
    certificate-fiber nonemptiness, and any compatible local certificate family that already admits
    a glued witness is forced by separatedness to glue uniquely.
    prop:typed-address-biaxial-completion-readable-fiber -/
theorem paper_typed_address_biaxial_completion_readable_fiber
    {Addr Cert Section Piece ι : Type}
    (read : Addr → Option Cert) (F : Addr → Set Cert)
    (restrict : ι → Section → Piece) (a : Addr) (locals : ι → Piece)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty)
    (hGlue : ∃ s : Section, ∀ i : ι, restrict i s = locals i)
    (hinj : Function.Injective (fun s : Section => fun i : ι => restrict i s)) :
    (read a ≠ none ↔ (F a).Nonempty) ∧
      ∃! s : Section, ∀ i : ι, restrict i s = locals i := by
  have hReadable :
      read a ≠ none ↔ (F a).Nonempty :=
    Omega.Topos.LocalSectionCriterion.paper_typed_address_biaxial_completion_local_section_package
      read F hcompat a
  rcases hGlue with ⟨s₀, hs₀⟩
  have hsep :
      ∀ s t : Section, (∀ i : ι, restrict i s = restrict i t) → s = t :=
    (Omega.RecursiveAddressing.paper_recursive_addressing_readout_separatedness_null
      restrict).2 hinj
  refine ⟨hReadable, ⟨s₀, hs₀, ?_⟩⟩
  intro t ht
  exact hsep t s₀ (fun i => (ht i).trans (hs₀ i).symm)

end Omega.TypedAddressBiaxialCompletion
