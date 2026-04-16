namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the geometric-harmonic tail lemma in the ETDS
    Chebotarev section.
    lem:geometric-harmonic-tail -/
theorem paper_etds_geometric_harmonic_tail
    (geometricDecay explicitTailBound controlledTailRemainder : Prop)
    (hBound : geometricDecay → explicitTailBound)
    (hRemainder : explicitTailBound → controlledTailRemainder) :
    geometricDecay → explicitTailBound ∧ controlledTailRemainder := by
  intro hDecay
  have hTail : explicitTailBound := hBound hDecay
  exact ⟨hTail, hRemainder hTail⟩

end Omega.Zeta
