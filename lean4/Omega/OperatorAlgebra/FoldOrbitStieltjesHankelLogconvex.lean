import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldOrbitMgfFiberFactorization

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The seed nonnegative random variable used to package the fold-orbit moments. -/
def foldOrbitStieltjesRandomVariable {m : ℕ} (N : Fin m → ℕ) : ℝ :=
  foldGaugeGroupOrder N

/-- The resulting Stieltjes moment sequence. -/
def foldOrbitStieltjesMoment {m : ℕ} (N : Fin m → ℕ) (q : ℕ) : ℝ :=
  foldOrbitStieltjesRandomVariable N ^ q

/-- Quadratic form of the Hankel matrix attached to the seed moment sequence. -/
def foldOrbitHankelQuadratic {m : ℕ} (N : Fin m → ℕ) (n : ℕ) (a : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, a i * foldOrbitStieltjesRandomVariable N ^ (i : ℕ)) ^ 2

/-- The fold-orbit seed moments come from a nonnegative random variable, so their Hankel quadratic
forms are squares and the sequence is log-convex.
    prop:op-algebra-fold-orbit-stieltjes-hankel-logconvex -/
theorem paper_op_algebra_fold_orbit_stieltjes_hankel_logconvex {m : ℕ} (N : Fin m → ℕ) :
    (∃ F : ℝ, 0 ≤ F ∧ ∀ q : ℕ, foldOrbitStieltjesMoment N q = F ^ q) ∧
      (∀ n : ℕ, ∀ a : Fin (n + 1) → ℝ, 0 ≤ foldOrbitHankelQuadratic N n a) ∧
      (∀ q : ℕ, 1 ≤ q →
        foldOrbitStieltjesMoment N q ^ 2 =
          foldOrbitStieltjesMoment N (q - 1) * foldOrbitStieltjesMoment N (q + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨foldOrbitStieltjesRandomVariable N, ?_, ?_⟩
    · simpa [foldOrbitStieltjesRandomVariable] using
        (show (0 : ℝ) ≤ (foldGaugeGroupOrder N : ℝ) by
          exact_mod_cast Nat.zero_le (foldGaugeGroupOrder N))
    intro q
    rfl
  · intro n a
    dsimp [foldOrbitHankelQuadratic]
    positivity
  · intro q hq
    have hsum : q + q = (q - 1) + (q + 1) := by
      omega
    rw [foldOrbitStieltjesMoment, foldOrbitStieltjesMoment, foldOrbitStieltjesMoment,
      pow_two, ← pow_add, ← pow_add]
    rw [hsum]

end Omega.OperatorAlgebra
