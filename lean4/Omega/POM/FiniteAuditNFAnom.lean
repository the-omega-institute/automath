import Omega.POM.SemConservativeOnSlice

namespace Omega.POM

/-- Paper label: `cor:pom-finite-audit-nf-anom`. On a bounded slice, if the finite audit signature
determines both the normal-form semantic output and the anomaly/spectral fingerprint, then equality
of that finite signature forces the semantic comparison data needed for the existing conservative
slice theorem, hence yields both the induced natural isomorphism and the algorithmic equivalence. -/
theorem paper_pom_finite_audit_nf_anom {α σ τ υ : Type*}
    (finiteSignature : α → σ) (SemNF : α → τ) (SemAnom : α → υ)
    (iso algEq : α → α → Prop)
    (hFinite :
      ∀ {w₁ w₂ : α}, finiteSignature w₁ = finiteSignature w₂ →
        SemNF w₁ = SemNF w₂ ∧ SemAnom w₁ = SemAnom w₂)
    (hSem :
      ∀ {w₁ w₂ : α}, SemNF w₁ = SemNF w₂ → SemAnom w₁ = SemAnom w₂ → algEq w₁ w₂)
    (hIso : ∀ {w₁ w₂ : α}, algEq w₁ w₂ → iso w₁ w₂) :
    ∀ {w₁ w₂ : α}, finiteSignature w₁ = finiteSignature w₂ → iso w₁ w₂ ∧ algEq w₁ w₂ := by
  intro w₁ w₂ hSig
  rcases hFinite hSig with ⟨hNF, hAnom⟩
  exact paper_pom_sem_conservative_on_slice SemNF SemAnom iso algEq hSem hIso hNF hAnom

end Omega.POM
