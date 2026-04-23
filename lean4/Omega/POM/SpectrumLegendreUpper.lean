import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-spectrum-legendre-upper`. -/
theorem paper_pom_spectrum_legendre_upper (f τ : ℝ → ℝ) :
    (∀ q γ : ℝ, 2 ≤ q → 0 ≤ γ → f γ ≤ τ q - q * γ) →
      ∀ γ : ℝ, 0 ≤ γ → f γ ≤ sInf {x : ℝ | ∃ q : ℝ, 2 ≤ q ∧ x = τ q - q * γ} := by
  intro hbound γ hγ
  have hnonempty : Set.Nonempty {x : ℝ | ∃ q : ℝ, 2 ≤ q ∧ x = τ q - q * γ} := by
    refine ⟨τ 2 - 2 * γ, 2, le_rfl, rfl⟩
  exact le_csInf hnonempty (by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact hbound q γ hq hγ)

end Omega.POM
