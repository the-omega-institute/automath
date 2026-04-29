import Mathlib.Tactic
import Omega.Zeta.XiKernelLossDivisibilityValuationRationalEuler

namespace Omega.Conclusion

open Omega.Zeta

/-- Rank-two ordered Smith data. -/
structure conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair where
  d1 : ℕ+
  d2 : ℕ+
  ordered : (d1 : ℕ) ∣ (d2 : ℕ)

/-- Axis-aligned ellipses ordered by divisibility of the two axes. -/
structure conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipse where
  a : ℕ+
  b : ℕ+
  ordered : (a : ℕ) ∣ (b : ℕ)

/-- Coordinatewise multiplication on ordered Smith pairs. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pairMul
    (x y : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair) :
    conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair :=
  ⟨x.d1 * y.d1, x.d2 * y.d2, Nat.mul_dvd_mul x.ordered y.ordered⟩

/-- Coordinatewise multiplication on ordered ellipses. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipseMul
    (E F : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipse) :
    conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipse :=
  ⟨E.a * F.a, E.b * F.b, Nat.mul_dvd_mul E.ordered F.ordered⟩

/-- Send a Smith pair to the ellipse with the same ordered axes. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse
    (x : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair) :
    conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipse :=
  ⟨x.d1, x.d2, x.ordered⟩

/-- Read the ordered axis lengths back as a Smith pair. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_fromEllipse
    (E : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipse) :
    conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair :=
  ⟨E.a, E.b, E.ordered⟩

/-- The length-two valuation profile attached to a prime and an ordered Smith pair. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_valuationProfile (p : ℕ)
    (x : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair) : Fin 2 → ℕ
  | ⟨0, _⟩ => ((x.d1 : ℕ).factorization p)
  | ⟨1, _⟩ => ((x.d2 : ℕ).factorization p)

/-- The transported p-primary kernel profile. -/
def conclusion_smith_ranktwo_divisibility_ellipse_semigroup_localKernel (n p : ℕ)
    (x : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair) (k : ℕ) : ℕ :=
  p ^ (k * (n - 2) +
    smithPrefixValue
      (conclusion_smith_ranktwo_divisibility_ellipse_semigroup_valuationProfile p x) k)

lemma conclusion_smith_ranktwo_divisibility_ellipse_semigroup_left_inv :
    Function.LeftInverse conclusion_smith_ranktwo_divisibility_ellipse_semigroup_fromEllipse
      conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse := by
  intro x
  cases x
  rfl

lemma conclusion_smith_ranktwo_divisibility_ellipse_semigroup_right_inv :
    Function.RightInverse conclusion_smith_ranktwo_divisibility_ellipse_semigroup_fromEllipse
      conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse := by
  intro E
  cases E
  rfl

lemma conclusion_smith_ranktwo_divisibility_ellipse_semigroup_smithPrefixValue
    (p k : ℕ) (x : conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pair) :
    smithPrefixValue
        (conclusion_smith_ranktwo_divisibility_ellipse_semigroup_valuationProfile p x) k =
      Nat.min (((x.d1 : ℕ).factorization p)) k +
        Nat.min (((x.d2 : ℕ).factorization p)) k := by
  unfold smithPrefixValue
  simp [conclusion_smith_ranktwo_divisibility_ellipse_semigroup_valuationProfile]

/-- Paper label: `thm:conclusion-smith-ranktwo-divisibility-ellipse-semigroup`. Ordered rank-two
Smith pairs and divisibility-ordered ellipses are the same semigroup under coordinatewise
multiplication, and the p-primary kernel expression is exactly the Smith-prefix valuation formula
for the two coordinate valuations. -/
theorem paper_conclusion_smith_ranktwo_divisibility_ellipse_semigroup :
    (∀ x y,
      conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse
          (conclusion_smith_ranktwo_divisibility_ellipse_semigroup_pairMul x y) =
        conclusion_smith_ranktwo_divisibility_ellipse_semigroup_ellipseMul
          (conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse x)
          (conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse y)) ∧
    Function.Bijective conclusion_smith_ranktwo_divisibility_ellipse_semigroup_toEllipse ∧
    (∀ n p x k,
      conclusion_smith_ranktwo_divisibility_ellipse_semigroup_localKernel n p x k =
        p ^ (k * (n - 2) +
          Nat.min (((x.d1 : ℕ).factorization p)) k +
            Nat.min (((x.d2 : ℕ).factorization p)) k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rfl
  · refine
      ⟨Function.LeftInverse.injective
          conclusion_smith_ranktwo_divisibility_ellipse_semigroup_left_inv, ?_⟩
    intro E
    refine ⟨conclusion_smith_ranktwo_divisibility_ellipse_semigroup_fromEllipse E, ?_⟩
    exact conclusion_smith_ranktwo_divisibility_ellipse_semigroup_right_inv E
  · intro n p x k
    rw [conclusion_smith_ranktwo_divisibility_ellipse_semigroup_localKernel,
      conclusion_smith_ranktwo_divisibility_ellipse_semigroup_smithPrefixValue]
    ring_nf

end Omega.Conclusion
