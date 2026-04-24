import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Folding

/-- The independent-set partial sum ending in an unoccupied terminal vertex. -/
def zgStateA (n : ℕ) : ℚ := 2 - (1 / 2 : ℚ) ^ n

/-- The independent-set partial sum ending in an occupied terminal vertex. -/
def zgStateB (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ (n + 1)

/-- The partial Dirichlet-Euler value obtained by combining the two transfer states. -/
def zgDirichletEulerPartial (n : ℕ) : ℚ := zgStateA n + zgStateB n

/-- Paper label: `thm:killo-zg-dirichlet-matrix-euler`. -/
theorem paper_killo_zg_dirichlet_matrix_euler :
    (∀ n, zgStateA (n + 1) = zgStateA n + zgStateB n) ∧
      (∀ n, zgStateB (n + 1) = (1 / 2 : ℚ) * zgStateB n) ∧
      (∀ n, zgDirichletEulerPartial n = 2 - (1 / 2 : ℚ) ^ (n + 1)) ∧
      (∀ n, |zgDirichletEulerPartial n - 2| = (1 / 2 : ℚ) ^ (n + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    unfold zgStateA zgStateB
    rw [pow_succ]
    ring
  · intro n
    unfold zgStateB
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
    ring
  · intro n
    unfold zgDirichletEulerPartial zgStateA zgStateB
    rw [pow_succ]
    ring
  · intro n
    have hpow : 0 ≤ (1 / 2 : ℚ) ^ (n + 1) := by positivity
    calc
      |zgDirichletEulerPartial n - 2| = |-(1 / 2 : ℚ) ^ (n + 1)| := by
        unfold zgDirichletEulerPartial zgStateA zgStateB
        rw [pow_succ]
        ring_nf
      _ = |(1 / 2 : ℚ) ^ (n + 1)| := by rw [abs_neg]
      _ = (1 / 2 : ℚ) ^ (n + 1) := by exact abs_of_nonneg hpow

end Omega.Folding
