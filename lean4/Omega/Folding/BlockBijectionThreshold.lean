import Mathlib.Data.Set.Basic

namespace Omega.Folding

/-- The map on subtype languages induced by a raw-to-output block map. -/
def blockBijectionMap
    {RawBlock OutBlock : Type}
    (B : RawBlock → OutBlock)
    (rawLanguage : Set RawBlock)
    (outLanguage : Set OutBlock)
    (hImage : ∀ ⦃x : RawBlock⦄, x ∈ rawLanguage → B x ∈ outLanguage) :
    {x // x ∈ rawLanguage} → {y // y ∈ outLanguage} :=
  fun x => ⟨B x.1, hImage x.2⟩

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite-block losslessness theorem in the
    rigidity reconstruction section.
    thm:block-bijection-threshold -/
theorem paper_resolution_folding_block_bijection_threshold
    {RawBlock OutBlock : Type}
    (B : RawBlock → OutBlock)
    (rawLanguage : Set RawBlock)
    (outLanguage : Set OutBlock)
    (hImage : ∀ ⦃x : RawBlock⦄, x ∈ rawLanguage → B x ∈ outLanguage)
    (hSurj : ∀ ⦃y : OutBlock⦄, y ∈ outLanguage → ∃ x ∈ rawLanguage, B x = y)
    (hInj : Set.InjOn B rawLanguage) :
    Function.Bijective (blockBijectionMap B rawLanguage outLanguage hImage) := by
  constructor
  · intro x₁ x₂ hEq
    apply Subtype.ext
    exact hInj x₁.2 x₂.2 (congrArg Subtype.val hEq)
  · intro y
    rcases hSurj y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

end Omega.Folding
