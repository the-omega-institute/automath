namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the minimal visible quotient lemma in the
    recursive addressing prefix-site paper.
    prop:prefix-site-min-visible-quotient -/
theorem paper_recursive_addressing_prefix_site_min_visible_quotient
    {A Avis B ι : Type}
    [Zero Avis]
    (defect : ι → A)
    (q : A → Avis)
    (φ : A → B)
    (KillsDefects : (A → B) → Prop)
    (hKills : KillsDefects φ)
    (hTrivial : ∀ i, q (defect i) = 0)
    (hFactor :
      KillsDefects φ →
        ∃ φbar : Avis → B, φ = φbar ∘ q ∧
          ∀ ψ : Avis → B, φ = ψ ∘ q → ψ = φbar) :
    (∀ i, q (defect i) = 0) ∧
      ∃ φbar : Avis → B, φ = φbar ∘ q ∧
        ∀ ψ : Avis → B, φ = ψ ∘ q → ψ = φbar := by
  exact ⟨hTrivial, hFactor hKills⟩

end Omega.RecursiveAddressing
