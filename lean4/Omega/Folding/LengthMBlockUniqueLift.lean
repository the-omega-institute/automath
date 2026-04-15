import Mathlib.Data.Set.Basic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the unique raw lift of a length-`m`
    output block in the rigidity reconstruction section.
    thm:length-m-block-unique-lift -/
theorem paper_resolution_folding_length_m_block_unique_lift
    {RawBlock OutBlock : Type}
    (B : RawBlock → OutBlock)
    (rawLanguage : Set RawBlock)
    (outLanguage : Set OutBlock)
    (hSurj : ∀ ⦃y : OutBlock⦄, y ∈ outLanguage → ∃ x ∈ rawLanguage, B x = y)
    (hInj : Set.InjOn B rawLanguage) :
    ∀ ⦃y : OutBlock⦄, y ∈ outLanguage → ∃! x, x ∈ rawLanguage ∧ B x = y := by
  intro y hy
  rcases hSurj hy with ⟨x, hx, rfl⟩
  refine ⟨x, ⟨hx, rfl⟩, ?_⟩
  intro x' hx'
  rcases hx' with ⟨hx'raw, hx'eq⟩
  apply hInj hx'raw hx
  simpa using hx'eq

end Omega.Folding
