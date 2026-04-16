import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- If a typed readout is compatible with the certificate fiber criterion, then `NULL` is exactly
the empty-fiber branch and non-`NULL` is exactly the nonempty-fiber branch.
    prop:typed-address-biaxial-completion-null-fiber -/
theorem paper_typed_address_biaxial_completion_null_fiber {Addr Cert : Type}
    (read : Addr → Option Cert) (F : Addr → Set Cert)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty) (a : Addr) :
    (read a = none ↔ F a = ∅) ∧ (read a ≠ none ↔ (F a).Nonempty) := by
  have hnonnull : read a ≠ none ↔ (F a).Nonempty := by
    rw [← Option.isSome_iff_ne_none]
    exact hcompat a
  refine ⟨?_, hnonnull⟩
  constructor
  · intro hnone
    ext c
    constructor
    · intro hc
      exact False.elim ((hnonnull.mpr ⟨c, hc⟩) hnone)
    · intro hc
      cases hc
  · intro hempty
    by_contra hnone
    exact ((hnonnull.mp hnone).ne_empty hempty)

end Omega.TypedAddressBiaxialCompletion
