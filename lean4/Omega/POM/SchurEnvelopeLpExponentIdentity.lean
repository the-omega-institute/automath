import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-schur-envelope-lp-exponent-identity`. -/
theorem paper_pom_schur_envelope_lp_exponent_identity
    (growthExponent : (ℕ → ℝ) → ℝ) (F₂ Fp : ℕ → ℝ) (Λ C : ℝ)
    (h₂ : growthExponent F₂ = Real.log Λ)
    (hConst : ∀ G : ℕ → ℝ, growthExponent (fun m => Real.exp C * G m) = growthExponent G)
    (hSandwich :
      (∀ m, F₂ m ≤ Fp m) ∧ (∀ m, Fp m ≤ Real.exp C * F₂ m))
    (hMono : ∀ A B : ℕ → ℝ, (∀ m, A m ≤ B m) → growthExponent A ≤ growthExponent B) :
    growthExponent Fp = Real.log Λ := by
  rcases hSandwich with ⟨hLower, hUpper⟩
  apply le_antisymm
  · calc
      growthExponent Fp ≤ growthExponent (fun m => Real.exp C * F₂ m) :=
        hMono Fp (fun m => Real.exp C * F₂ m) hUpper
      _ = growthExponent F₂ := hConst F₂
      _ = Real.log Λ := h₂
  · calc
      Real.log Λ = growthExponent F₂ := h₂.symm
      _ ≤ growthExponent Fp := hMono F₂ Fp hLower

end Omega.POM
