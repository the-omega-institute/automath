namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for higher-block identification with the full
    two-shift in the rigidity reconstruction section.
    cor:higher-block-identification -/
theorem paper_resolution_folding_higher_block_identification
    {RawBlock OutBlock : Type}
    (B : RawBlock → OutBlock)
    (ConsecutiveRaw : RawBlock → RawBlock → Prop)
    (ConsecutiveOut : OutBlock → OutBlock → Prop)
    (hForward : ∀ ⦃x x' : RawBlock⦄, ConsecutiveRaw x x' → ConsecutiveOut (B x) (B x'))
    (hBackward :
      ∀ ⦃y y' : OutBlock⦄, ConsecutiveOut y y' →
        ∃ x x', B x = y ∧ B x' = y' ∧ ConsecutiveRaw x x') :
    ∀ ⦃y y' : OutBlock⦄, ConsecutiveOut y y' ↔
      ∃ x x', B x = y ∧ B x' = y' ∧ ConsecutiveRaw x x' := by
  intro y y'
  constructor
  · intro hConsecutive
    exact hBackward hConsecutive
  · rintro ⟨x, x', rfl, rfl, hConsecutive⟩
    exact hForward hConsecutive

end Omega.Folding
