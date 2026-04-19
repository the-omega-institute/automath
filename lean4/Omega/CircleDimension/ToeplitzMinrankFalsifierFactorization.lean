import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Canonical positive block used in the minimal falsifier model. -/
def toeplitzCanonicalQN (κ : ℕ) : Matrix (Fin κ) (Fin κ) ℂ := 0

/-- Canonical falsifier block: the identity matrix witnesses all `κ` negative directions. -/
def toeplitzCanonicalWN (κ : ℕ) : Matrix (Fin κ) (Fin κ) ℂ := 1

/-- The explicit negative block factors through the identity falsifier, which has full rank; any
exact decomposition with zero positive part therefore needs rank at least `κ`.
    thm:xi-toeplitz-minrank-falsifier-factorization -/
theorem paper_xi_toeplitz_minrank_falsifier_factorization (κ : ℕ) :
    (-(1 : Matrix (Fin κ) (Fin κ) ℂ) =
      toeplitzCanonicalQN κ - (toeplitzCanonicalWN κ).conjTranspose * toeplitzCanonicalWN κ) ∧
      (toeplitzCanonicalWN κ).rank = κ ∧
      (∀ x : Fin κ → ℂ, (toeplitzCanonicalWN κ).mulVec x = 0 → x = 0) ∧
      (∀ W : Matrix (Fin κ) (Fin κ) ℂ,
        (-(1 : Matrix (Fin κ) (Fin κ) ℂ) = (0 : Matrix (Fin κ) (Fin κ) ℂ) - W.conjTranspose * W) →
        κ ≤ W.rank) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [toeplitzCanonicalQN, toeplitzCanonicalWN]
  · simpa [toeplitzCanonicalWN] using (Matrix.rank_one (R := ℂ) (n := Fin κ))
  · intro x hx
    simpa [toeplitzCanonicalWN] using hx
  · intro W hW
    have hWW : W.conjTranspose * W = (1 : Matrix (Fin κ) (Fin κ) ℂ) := by
      apply neg_injective
      simpa using hW.symm
    calc
      κ = (1 : Matrix (Fin κ) (Fin κ) ℂ).rank := by
        simpa using (Matrix.rank_one (R := ℂ) (n := Fin κ)).symm
      _ = (W.conjTranspose * W).rank := by simpa [hWW]
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _

end Omega.CircleDimension
