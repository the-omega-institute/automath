import Mathlib.Tactic

namespace Omega.POM

/-- The original ordered pair of fiber masses. -/
def fineFiberPair (a b : ℝ) : ℝ × ℝ :=
  (a, b)

/-- Coarse-graining merges the second block into the first one and zeroes the tail coordinate. -/
def coarseFiberPair (a b : ℝ) : ℝ × ℝ :=
  (a + b, 0)

/-- For two coordinates, majorization is equivalent to domination of the first prefix sum together
with preservation of the total mass. -/
def pairMajorizes (x y : ℝ × ℝ) : Prop :=
  y.1 ≤ x.1 ∧ y.1 + y.2 = x.1 + x.2

/-- The descending-order hypothesis on a two-coordinate profile. -/
def pairSortedDescending (x : ℝ × ℝ) : Prop :=
  x.2 ≤ x.1

/-- A basic Schur-convex proxy: the squared Euclidean energy. -/
def pairSquareEnergy (x : ℝ × ℝ) : ℝ :=
  x.1 ^ (2 : ℕ) + x.2 ^ (2 : ℕ)

/-- A basic Schur-concave proxy: the tail mass outside the leading block. -/
def pairTailMass (x : ℝ × ℝ) : ℝ :=
  x.2

/-- A single coarse-graining merge on a sorted nonnegative pair preserves the total mass, enlarges
the leading prefix sum, increases the Schur-convex square energy, and decreases the tail mass.
This is the two-coordinate seed of the paper's coarse-graining/majorization principle.
    thm:pom-coarsegraining-majorization-schur -/
theorem paper_pom_coarsegraining_majorization_schur (a b : ℝ) (hab : b ≤ a) (hb : 0 ≤ b) :
    pairSortedDescending (fineFiberPair a b) ∧
      pairMajorizes (coarseFiberPair a b) (fineFiberPair a b) ∧
      pairSquareEnergy (fineFiberPair a b) ≤ pairSquareEnergy (coarseFiberPair a b) ∧
      pairTailMass (coarseFiberPair a b) ≤ pairTailMass (fineFiberPair a b) := by
  have ha : 0 ≤ a := le_trans hb hab
  constructor
  · simpa [pairSortedDescending, fineFiberPair] using hab
  constructor
  · constructor
    · have hab' : a ≤ a + b := by linarith
      simpa [pairMajorizes, fineFiberPair, coarseFiberPair] using hab'
    · simp [fineFiberPair, coarseFiberPair]
  constructor
  · dsimp [pairSquareEnergy, fineFiberPair, coarseFiberPair]
    nlinarith
  · simpa [pairTailMass, fineFiberPair, coarseFiberPair] using hb

end Omega.POM
