import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete prime-support model for the one-circle internalization. The set `primeSupport`
records the prime registers appearing in the kernel. -/
structure conclusion_infinite_primes_one_circle_data where
  conclusion_infinite_primes_one_circle_primeSupport : Set ℕ
  conclusion_infinite_primes_one_circle_support_primes :
    ∀ p ∈ conclusion_infinite_primes_one_circle_primeSupport, Nat.Prime p

namespace conclusion_infinite_primes_one_circle_data

noncomputable def pFiberDimension (D : conclusion_infinite_primes_one_circle_data) (p : ℕ) :
    ℕ := by
  classical
  exact if p ∈ D.conclusion_infinite_primes_one_circle_primeSupport then 1 else 0

noncomputable def pcdimEqOne (D : conclusion_infinite_primes_one_circle_data) : Prop := by
  classical
  exact
    (∀ p : ℕ, Nat.Prime p →
      D.pFiberDimension p =
        if p ∈ D.conclusion_infinite_primes_one_circle_primeSupport then 1 else 0) ∧
      (∀ p : ℕ, D.pFiberDimension p ≤ 1)

def existsOneCircleExtension (D : conclusion_infinite_primes_one_circle_data) : Prop :=
  ∃ circleRank : ℕ,
    circleRank = 1 ∧
      ∀ p : ℕ, D.pFiberDimension p ≤ circleRank

def compactLieModel (D : conclusion_infinite_primes_one_circle_data) : Prop :=
  D.conclusion_infinite_primes_one_circle_primeSupport.Finite

def infiniteNotCompactLie (D : conclusion_infinite_primes_one_circle_data) : Prop :=
  D.conclusion_infinite_primes_one_circle_primeSupport.Infinite → ¬ D.compactLieModel

end conclusion_infinite_primes_one_circle_data

/-- Paper label: `cor:conclusion-infinite-primes-one-circle`. The direct-product prime register
has one-dimensional fiber at primes in the support and zero otherwise, so one circle dominates all
fibers; an infinite prime support cannot be compact-Lie in this finite-support obstruction model. -/
theorem paper_conclusion_infinite_primes_one_circle
    (D : conclusion_infinite_primes_one_circle_data) :
    D.pcdimEqOne ∧ D.existsOneCircleExtension ∧ D.infiniteNotCompactLie := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro p hp
      simp [conclusion_infinite_primes_one_circle_data.pFiberDimension]
    · intro p
      unfold conclusion_infinite_primes_one_circle_data.pFiberDimension
      split <;> omega
  · refine ⟨1, rfl, ?_⟩
    intro p
    exact (show D.pFiberDimension p ≤ 1 from by
      unfold conclusion_infinite_primes_one_circle_data.pFiberDimension
      split <;> omega)
  · intro hinfinite hcompact
    exact hinfinite hcompact

end Omega.Conclusion
