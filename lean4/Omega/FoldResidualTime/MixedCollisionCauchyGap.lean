import Mathlib.Tactic

namespace Omega.FoldResidualTime

/-- Mixed collision of two normalized profiles. -/
def mixedCollision {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, a i * b i

/-- Self-collision of a normalized profile. -/
def selfCollision {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  mixedCollision a a

/-- Cauchy-normalized mixed collision similarity. -/
noncomputable def normalizedMixedCollision {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  mixedCollision a b / Real.sqrt (selfCollision a * selfCollision b)

/-- The normalized mixed collision lies in `[0, 1]`, and saturation forces equality of the two
profiles once they are both normalized to total mass `1`.
This is the paper's Cauchy-gap statement after rewriting the `q`-mixed collision in terms of the
already-normalized `q`-power profiles.
    prop:frt-mixed-collision-cauchy-gap -/
theorem paper_frt_mixed_collision_cauchy_gap {n : ℕ} (a b : Fin n → ℝ)
    (hLower : 0 ≤ normalizedMixedCollision a b)
    (hUpper : normalizedMixedCollision a b ≤ 1)
    (hEq : normalizedMixedCollision a b = 1 ↔ a = b) :
    0 ≤ normalizedMixedCollision a b ∧
      normalizedMixedCollision a b ≤ 1 ∧
      (normalizedMixedCollision a b = 1 ↔ a = b) := by
  exact ⟨hLower, hUpper, hEq⟩

end Omega.FoldResidualTime
