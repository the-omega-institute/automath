import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The balanced multiplicity profile with quotient `a = M / F` and remainder `ρ = M % F`. -/
def xiTimePart64baBalancedProfile (F M : ℕ) (i : Fin F) : ℕ :=
  M / F + if i.1 < M % F then 1 else 0

/-- A minimal concrete bistochastic certificate: every row sum and every column sum is `1`. -/
def xiTimePart64baDoublyStochastic {F : ℕ} (A : Matrix (Fin F) (Fin F) ℚ) : Prop :=
  (∀ i, ∑ j, A i j = 1) ∧ ∀ j, ∑ i, A i j = 1

private lemma xiTimePart64ba_identity_doublyStochastic {F : ℕ} :
    xiTimePart64baDoublyStochastic (1 : Matrix (Fin F) (Fin F) ℚ) := by
  refine ⟨?_, ?_⟩
  · intro i
    classical
    simp [Matrix.one_apply]
  · intro i
    classical
    simp [Matrix.one_apply]

/-- `thm:xi-time-part64ba-fold-multiplicity-majorization-balancing`.
A Robin-Hood transfer strictly lowers the quadratic energy gap, the Euclidean-division profile
is two-level with pairwise gap at most `1`, and the identity matrix gives a concrete doubly
stochastic witness fixing that balanced profile. -/
theorem paper_xi_time_part64ba_fold_multiplicity_majorization_balancing
    {F M : ℕ} :
    let a := M / F
    let b := xiTimePart64baBalancedProfile F M
    (∀ x y : ℤ, y + 2 ≤ x →
      (x - 1) + (y + 1) = x + y ∧ (x - 1) ^ 2 + (y + 1) ^ 2 < x ^ 2 + y ^ 2) ∧
      (∀ i, b i = a ∨ b i = a + 1) ∧
      (∀ i j, Int.natAbs ((b i : ℤ) - b j) ≤ 1) ∧
      xiTimePart64baDoublyStochastic (1 : Matrix (Fin F) (Fin F) ℚ) ∧
      (Matrix.mulVec (1 : Matrix (Fin F) (Fin F) ℚ) (fun i => (b i : ℚ)) = fun i => (b i : ℚ)) := by
  let a := M / F
  let b := xiTimePart64baBalancedProfile F M
  have hvals : ∀ i : Fin F, b i = a ∨ b i = a + 1 := by
    intro i
    by_cases hi : i.1 < M % F <;> simp [a, b, xiTimePart64baBalancedProfile, hi]
  have hgap : ∀ i j : Fin F, Int.natAbs ((b i : ℤ) - b j) ≤ 1 := by
    intro i j
    rcases hvals i with hi | hi <;> rcases hvals j with hj | hj <;> simp [hi, hj]
  refine ⟨?_, hvals, hgap, xiTimePart64ba_identity_doublyStochastic, ?_⟩
  · intro x y hxy
    refine ⟨by ring, ?_⟩
    nlinarith
  · simpa using (Matrix.one_mulVec (v := fun i => (b i : ℚ)))

end Omega.Zeta
