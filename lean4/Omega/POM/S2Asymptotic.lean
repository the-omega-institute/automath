import Mathlib.Data.Real.Basic

/--
Packaging of an existing `S₂` asymptotic certificate and its collision-scale
transfer through division by `4^m`.

cor:pom-s2-asymptotic
-/
theorem paper_pom_s2_asymptotic (S2 collision : ℕ → ℝ) (r2 : ℝ)
    (Theta : (ℕ → ℝ) → ℝ → Prop) (hS2 : Theta S2 r2)
    (hcollision : ∀ m, collision m = S2 m / (4 : ℝ)^m)
    (hTheta_map : Theta S2 r2 → (∀ m, collision m = S2 m / (4 : ℝ)^m) →
      Theta collision (r2 / 4)) :
    Theta S2 r2 ∧ Theta collision (r2 / 4) := by
  exact ⟨hS2, hTheta_map hS2 hcollision⟩
