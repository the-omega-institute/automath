import Mathlib.Tactic

/-!
# Fibadic lcm filtration law seeds

This file registers the paper-facing seed/package wrapper for
`thm:conclusion-fibadic-finite-layer-lcm-filtration-law`.
-/

namespace Omega.Conclusion.FibadicLcmFiltrationLaw

/-- Paper seed for the fibadic lcm filtration law.
    If the filtration is closed under addition and multiplication at lcm depth,
    then the conductor depth of `f + g` and `f * g` divides `lcm (D f) (D g)`.
    thm:conclusion-fibadic-finite-layer-lcm-filtration-law -/
theorem paper_conclusion_fibadic_lcm_filtration_law_seeds
    {α : Type} [Add α] [Mul α] (H : ℕ → Set α) (D : α → ℕ)
    (hadd : ∀ {d e : ℕ} {f g : α}, f ∈ H d → g ∈ H e → f + g ∈ H (Nat.lcm d e))
    (hmul : ∀ {d e : ℕ} {f g : α}, f ∈ H d → g ∈ H e → f * g ∈ H (Nat.lcm d e))
    (hmem : ∀ f : α, f ∈ H (D f))
    (hmin : ∀ {f : α} {d : ℕ}, f ∈ H d → D f ∣ d)
    (f g : α) :
    D (f + g) ∣ Nat.lcm (D f) (D g) ∧ D (f * g) ∣ Nat.lcm (D f) (D g) := by
  refine ⟨hmin (hadd (hmem f) (hmem g)), hmin (hmul (hmem f) (hmem g))⟩

/-- Packaged form of the fibadic lcm filtration law seeds.
    thm:conclusion-fibadic-finite-layer-lcm-filtration-law -/
theorem paper_conclusion_fibadic_lcm_filtration_law_package
    {α : Type} [Add α] [Mul α] (H : ℕ → Set α) (D : α → ℕ)
    (hadd : ∀ {d e : ℕ} {f g : α}, f ∈ H d → g ∈ H e → f + g ∈ H (Nat.lcm d e))
    (hmul : ∀ {d e : ℕ} {f g : α}, f ∈ H d → g ∈ H e → f * g ∈ H (Nat.lcm d e))
    (hmem : ∀ f : α, f ∈ H (D f))
    (hmin : ∀ {f : α} {d : ℕ}, f ∈ H d → D f ∣ d)
    (f g : α) :
    D (f + g) ∣ Nat.lcm (D f) (D g) ∧ D (f * g) ∣ Nat.lcm (D f) (D g) :=
  paper_conclusion_fibadic_lcm_filtration_law_seeds H D hadd hmul hmem hmin f g

end Omega.Conclusion.FibadicLcmFiltrationLaw
