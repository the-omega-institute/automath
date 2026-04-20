import Omega.TypedAddressBiaxialCompletion.NullFiber
import Omega.TypedAddressBiaxialCompletion.ReadableFiber

namespace Omega.CircleDimension

/-- A circle-dimension readout is non-`NULL` exactly when its certificate fiber is nonempty, while
the `NULL` branch is exactly fiber emptiness; for a finite cover, any compatible local witness
family glues uniquely once the restriction tuple separates global sections.
    prop:cdim-nonnull-section-criterion -/
theorem paper_cdim_nonnull_section_criterion
    {Addr Cert Section Piece ι : Type}
    (read : Addr → Option Cert) (F : Addr → Set Cert)
    (restrict : ι → Section → Piece) (a : Addr) (locals : ι → Piece)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty)
    (hGlue : ∃ s : Section, ∀ i : ι, restrict i s = locals i)
    (hinj : Function.Injective (fun s : Section => fun i : ι => restrict i s)) :
    (read a = none ↔ F a = ∅) ∧
    (read a ≠ none ↔ (F a).Nonempty) ∧
    ∃! s : Section, ∀ i : ι, restrict i s = locals i := by
  have hnull :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_null_fiber
      read F hcompat a
  have hread :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_readable_fiber
      read F restrict a locals hcompat hGlue hinj
  exact ⟨hnull.1, hread.1, hread.2⟩

end Omega.CircleDimension
