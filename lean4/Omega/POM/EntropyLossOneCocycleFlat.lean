import Omega.POM.EntropyLossFactorChainExpansion

namespace Omega.POM

/-- Paper label: `thm:pom-entropy-loss-1cocycle-flat`. -/
theorem paper_pom_entropy_loss_1cocycle_flat (P : ℕ → ℝ) (a b c : ℕ) :
    let H : ℕ → ℕ → ℝ := fun x y => (y : ℝ) * P x - P (x * y)
    H a (b * c) = (c : ℝ) * H a b + H (a * b) c := by
  dsimp
  rw [Nat.mul_assoc]
  norm_num [Nat.cast_mul]
  ring

end Omega.POM
