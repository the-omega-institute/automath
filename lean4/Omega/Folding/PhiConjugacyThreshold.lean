namespace Omega.Folding

universe u v w

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact local inverse rules for `Phi_m` in the rigidity
    reconstruction section.
    thm:Phi-m-conjugacy-threshold -/
theorem paper_resolution_folding_phi_m_conjugacy_threshold
    {X : Type u} {Y : Type v} {Window : Type w}
    (Φ : X → Y) (Ψ : Window → Y → X)
    (localRule : Window → Prop)
    (hLocal : ∀ r, localRule r)
    (hInv : ∀ r, Function.LeftInverse (Ψ r) Φ ∧ Function.RightInverse (Ψ r) Φ) :
    ∀ r, localRule r ∧ Function.LeftInverse (Ψ r) Φ ∧ Function.RightInverse (Ψ r) Φ := by
  intro r
  exact ⟨hLocal r, (hInv r).1, (hInv r).2⟩

end Omega.Folding
