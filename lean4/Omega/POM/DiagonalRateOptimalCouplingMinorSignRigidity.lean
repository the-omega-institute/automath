import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-diagonal-rate-optimal-coupling-minor-sign-rigidity`. -/
theorem paper_pom_diagonal_rate_optimal_coupling_minor_sign_rigidity {n : ℕ}
    (u : Fin n → ℝ) (κ Z : ℝ) :
    ∀ i j k l : Fin n,
      (let B : Fin n → Fin n → ℝ := fun a c => 1 + κ * if a = c then (1 : ℝ) else 0
       let P : Fin n → Fin n → ℝ := fun a c => u a * u c * B a c / Z
       P i k * P j l - P i l * P j k =
        u i * u j * u k * u l / Z ^ 2 * (B i k * B j l - B i l * B j k)) := by
  intro i j k l
  dsimp
  ring

end Omega.POM
