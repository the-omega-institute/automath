namespace Omega.Zeta

/-- Paper label: `thm:xi-toeplitz-psd-cofinal-sparsification-hereditary`. -/
theorem paper_xi_toeplitz_psd_cofinal_sparsification_hereditary (Phi : Nat → Prop)
    (hhered : ∀ {m n : Nat}, m ≤ n → Phi n → Phi m) (N : Nat → Nat)
    (hcofinal : ∀ m, ∃ j, m ≤ N j) : (∀ m, Phi m) ↔ ∀ j, Phi (N j) := by
  constructor
  · intro hPhi j
    exact hPhi (N j)
  · intro hcof m
    rcases hcofinal m with ⟨j, hmj⟩
    exact hhered hmj (hcof j)

/-- Paper label: `thm:xi-toeplitz-psd-cofinal-sparsification`. -/
theorem paper_xi_toeplitz_psd_cofinal_sparsification (Phi : Nat → Prop)
    (hhered : ∀ {m n : Nat}, m ≤ n → Phi n → Phi m) (N : Nat → Nat)
    (hcofinal : ∀ m, ∃ j, m ≤ N j) : ((∀ m, Phi m) ↔ ∀ j, Phi (N j)) := by
  exact paper_xi_toeplitz_psd_cofinal_sparsification_hereditary Phi hhered N hcofinal

end Omega.Zeta
