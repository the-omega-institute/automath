import Mathlib.Tactic

namespace Omega.SPG

/-- If each boundary Gödel code decodes the `m`-th dyadic outer approximation, then the whole
    code sequence determines the closure by intersecting those approximants.
    thm:spg-boundary-godel-sequence-determines-closure -/
theorem paper_spg_boundary_godel_sequence_determines_closure
    {α β : Type*}
    (closureA : Set α)
    (U : ℕ → Set α)
    (H : ℕ → β)
    (decode : β → Set α)
    (_hNested : ∀ m, U (m + 1) ⊆ U m)
    (hDecode : ∀ m, decode (H m) = U m)
    (hClosure : closureA = ⋂ m, U m) :
    closureA = ⋂ m, decode (H m) := by
  simpa [hDecode] using hClosure

end Omega.SPG
