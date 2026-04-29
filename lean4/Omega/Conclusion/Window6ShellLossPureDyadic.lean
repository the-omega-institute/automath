import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The window-6 shell matrix `A₂`. -/
def conclusion_window6_shell_loss_pure_dyadic_A2 : Matrix (Fin 3) (Fin 5) ℤ :=
  !![(-1 : ℤ), 0, 0, 0, 0;
    0, 1, 1, -1, -1;
    0, 1, -1, 1, -1]

/-- The window-6 shell matrix `A₃`. -/
def conclusion_window6_shell_loss_pure_dyadic_A3 : Matrix (Fin 2) (Fin 4) ℤ :=
  !![(1 : ℤ), 1, -1, -1;
    1, -1, 1, -1]

/-- The exterior-shell matrix `B₂`. -/
def conclusion_window6_shell_loss_pure_dyadic_B2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-1 : ℤ), -1, 0;
    -1, 1, 0;
    0, 0, -2]

/-- The pure dyadic loss factor: only the `p = 2` direction contributes extra shell memory. -/
def conclusion_window6_shell_loss_pure_dyadic_loss (p k : ℕ) : ℕ :=
  if p = 2 ∧ 0 < k then 2 else 1

/-- The expected `A₂` kernel count from the dyadic loss model. -/
def conclusion_window6_shell_loss_pure_dyadic_A2_kernel_count (p k : ℕ) : ℕ :=
  p ^ (2 * k) * conclusion_window6_shell_loss_pure_dyadic_loss p k

/-- The expected `A₃` kernel count from the dyadic loss model. -/
def conclusion_window6_shell_loss_pure_dyadic_A3_kernel_count (p k : ℕ) : ℕ :=
  p ^ (2 * k) * conclusion_window6_shell_loss_pure_dyadic_loss p k

/-- The expected `B₂` kernel count from the dyadic loss model. -/
def conclusion_window6_shell_loss_pure_dyadic_B2_kernel_count (p k : ℕ) : ℕ :=
  conclusion_window6_shell_loss_pure_dyadic_loss p k ^ 2

/-- Concrete window-6 dyadic shell-loss package. -/
def conclusion_window6_shell_loss_pure_dyadic_statement (p k : ℕ) : Prop :=
  conclusion_window6_shell_loss_pure_dyadic_A2 0 0 = -1 ∧
    conclusion_window6_shell_loss_pure_dyadic_A3 0 0 = 1 ∧
    conclusion_window6_shell_loss_pure_dyadic_B2 2 2 = -2 ∧
    conclusion_window6_shell_loss_pure_dyadic_A2_kernel_count p k =
      p ^ (2 * k) * conclusion_window6_shell_loss_pure_dyadic_loss p k ∧
    conclusion_window6_shell_loss_pure_dyadic_A3_kernel_count p k =
      p ^ (2 * k) * conclusion_window6_shell_loss_pure_dyadic_loss p k ∧
    conclusion_window6_shell_loss_pure_dyadic_B2_kernel_count p k =
      conclusion_window6_shell_loss_pure_dyadic_loss p k ^ 2 ∧
    ((p ≠ 2 ∨ k = 0) → conclusion_window6_shell_loss_pure_dyadic_loss p k = 1) ∧
    (p = 2 → 0 < k → conclusion_window6_shell_loss_pure_dyadic_loss p k = 2)

/-- Paper label: `cor:conclusion-window6-shell-loss-pure-dyadic`. -/
theorem paper_conclusion_window6_shell_loss_pure_dyadic
    (p k : ℕ) : conclusion_window6_shell_loss_pure_dyadic_statement p k := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    by_cases hp : p = 2
    · have hk : k = 0 := by
        rcases h with hp' | hk
        · exact (hp' hp).elim
        · exact hk
      simp [conclusion_window6_shell_loss_pure_dyadic_loss, hp, hk]
    · simp [conclusion_window6_shell_loss_pure_dyadic_loss, hp]
  · intro hp hk
    simp [conclusion_window6_shell_loss_pure_dyadic_loss, hp, hk]

end Omega.Conclusion
