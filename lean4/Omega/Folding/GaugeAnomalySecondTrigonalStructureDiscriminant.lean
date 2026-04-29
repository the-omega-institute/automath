import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Folding

/-- The affine cubic obtained from the second trigonal slice after setting `w = 1`. -/
def secondTrigonalCubic (t u : ℚ) : ℚ :=
  (t ^ 4 - t ^ 3 - t ^ 2) +
    (4 * t ^ 3 - 5 * t ^ 2 + 2) * u +
    (6 * t ^ 2 - 7 * t + 1) * u ^ 2 +
    (3 * t - 3) * u ^ 3

/-- The leading coefficient of `secondTrigonalCubic t`. -/
def secondTrigonalA (t : ℚ) : ℚ :=
  3 * t - 3

/-- The quadratic coefficient of `secondTrigonalCubic t`. -/
def secondTrigonalB (t : ℚ) : ℚ :=
  6 * t ^ 2 - 7 * t + 1

/-- The linear coefficient of `secondTrigonalCubic t`. -/
def secondTrigonalC (t : ℚ) : ℚ :=
  4 * t ^ 3 - 5 * t ^ 2 + 2

/-- The constant coefficient of `secondTrigonalCubic t`. -/
def secondTrigonalD (t : ℚ) : ℚ :=
  t ^ 4 - t ^ 3 - t ^ 2

/-- The explicit degree-`9` branch polynomial appearing in the second trigonal discriminant. -/
def secondTrigonalP9 (t : ℚ) : ℚ :=
  3 * t ^ 9 + 3 * t ^ 8 - 31 * t ^ 7 - 83 * t ^ 6 + 100 * t ^ 5 + 424 * t ^ 4 -
    16 * t ^ 3 - 436 * t ^ 2 - 52 * t + 100

/-- Discriminant of the cubic `a u^3 + b u^2 + c u + d`. -/
def secondTrigonalDisc (t : ℚ) : ℚ :=
  secondTrigonalB t ^ 2 * secondTrigonalC t ^ 2 -
    4 * secondTrigonalA t * secondTrigonalC t ^ 3 -
    4 * secondTrigonalB t ^ 3 * secondTrigonalD t -
    27 * secondTrigonalA t ^ 2 * secondTrigonalD t ^ 2 +
    18 * secondTrigonalA t * secondTrigonalB t * secondTrigonalC t * secondTrigonalD t

/-- Concrete branch support statement used to record that the `t = 1` factor is separated from the
degree-`9` branch factor. -/
def secondTrigonalSimpleBranchParameters : Prop :=
  (∀ t : ℚ, secondTrigonalDisc t = 0 → t = 1 ∨ secondTrigonalP9 t = 0) ∧ secondTrigonalP9 1 ≠ 0

/-- Paper label: `thm:fold-gauge-anomaly-second-trigonal-structure-discriminant`. -/
theorem paper_fold_gauge_anomaly_second_trigonal_structure_discriminant :
    (∀ t : Rat, secondTrigonalDisc t = -(t - 1) * secondTrigonalP9 t) ∧
      secondTrigonalSimpleBranchParameters := by
  refine ⟨?_, ?_⟩
  · intro t
    dsimp [secondTrigonalDisc, secondTrigonalA, secondTrigonalB, secondTrigonalC, secondTrigonalD,
      secondTrigonalP9]
    ring
  · refine ⟨?_, ?_⟩
    · intro t hdisc
      rw [show secondTrigonalDisc t = -(t - 1) * secondTrigonalP9 t by
        dsimp [secondTrigonalDisc, secondTrigonalA, secondTrigonalB, secondTrigonalC,
          secondTrigonalD, secondTrigonalP9]
        ring] at hdisc
      rcases mul_eq_zero.mp hdisc with hfactor | hp9
      · left
        linarith
      · right
        exact hp9
    · norm_num [secondTrigonalP9]

end Omega.Folding
