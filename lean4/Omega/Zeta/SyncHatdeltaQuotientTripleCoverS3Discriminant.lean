import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit cubic equation for the quotient triple cover over `ℚ(x)`. -/
def syncHatdeltaTripleCoverCubic (x y : ℚ) : ℚ :=
  x * y ^ 3 + (x ^ 2 - x) * y ^ 2 + (3 * x - 6 * x ^ 2 - 1) * y + (1 - 5 * x + 5 * x ^ 2 - x ^ 3)

/-- The discriminant of the displayed cubic, expanded as a polynomial in `x`. -/
def syncHatdeltaTripleCoverDiscriminant (x : ℚ) : ℚ :=
  4 * x ^ 9 + 85 * x ^ 8 + 416 * x ^ 7 - 818 * x ^ 6 + 1196 * x ^ 5 - 871 * x ^ 4 +
    284 * x ^ 3 - 44 * x ^ 2 + 4 * x

/-- The degree-`8` factor in the cubic discriminant. -/
def syncHatdeltaP8 (x : ℚ) : ℚ :=
  4 * x ^ 8 + 85 * x ^ 7 + 416 * x ^ 6 - 818 * x ^ 5 + 1196 * x ^ 4 - 871 * x ^ 3 +
    284 * x ^ 2 - 44 * x + 4

/-- The quadratic resolvent cover `v² = x P₈(x)` has degree `9` on the right-hand side. -/
def syncHatdeltaHyperellipticDegree : ℕ := 9

/-- Genus formula for an odd-degree hyperelliptic curve `v² = f(x)` with `deg f = 2g + 1`. -/
def syncHatdeltaHyperellipticGenus (d : ℕ) : ℕ := (d - 1) / 2

/-- `prop:sync-hatdelta-quotient-triple-cover-s3-discriminant`.
The cubic discriminant factors as `x P₈(x)`, its specialization at `x = -1` is negative and
hence not a rational square, and the associated hyperelliptic resolvent has genus `4`. -/
theorem paper_sync_hatdelta_quotient_triple_cover_s3_discriminant :
    (∀ x : ℚ,
      syncHatdeltaTripleCoverDiscriminant x = x * syncHatdeltaP8 x) ∧
      syncHatdeltaTripleCoverDiscriminant (-1) = -3552 ∧
      ¬ IsSquare (syncHatdeltaTripleCoverDiscriminant (-1)) ∧
      syncHatdeltaHyperellipticGenus syncHatdeltaHyperellipticDegree = 4 := by
  refine ⟨?_, by norm_num [syncHatdeltaTripleCoverDiscriminant], ?_, by native_decide⟩
  · intro x
    unfold syncHatdeltaTripleCoverDiscriminant syncHatdeltaP8
    ring
  · intro hsq
    rcases hsq with ⟨q, hq⟩
    have hnonneg : 0 ≤ syncHatdeltaTripleCoverDiscriminant (-1) := by
      simpa [hq, pow_two] using sq_nonneg q
    norm_num [syncHatdeltaTripleCoverDiscriminant] at hnonneg

end Omega.Zeta
