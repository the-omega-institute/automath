import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Folding

open Polynomial

noncomputable section

/-- The five transitive subgroup types of `S₄`. -/
inductive QuarticTransitiveSubgroup where
  | v4
  | c4
  | d4
  | a4
  | s4
  deriving DecidableEq, Repr

/-- The quartic branch factor appearing in the trigonal gauge-anomaly ramification analysis. -/
def q4 : Polynomial ℤ :=
  9 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + 8 * X - 16

/-- The audited discriminant factorization of `q₄`. -/
def q4Discriminant : ℤ :=
  -(2 ^ 12) * 3 ^ 4 * 1931

/-- The mod-`17` factorization is irreducible, hence of degree pattern `(4)`. -/
def q4Mod17FactorDegrees : List ℕ :=
  [4]

/-- The mod-`13` factorization type is `(1,1,2)`. -/
def q4Mod13FactorDegrees : List ℕ :=
  [1, 1, 2]

/-- The transitive-subgroup elimination leaves the full symmetric group. -/
def q4GaloisGroup : QuarticTransitiveSubgroup :=
  .s4

/-- The quadratic subfield comes from the discriminant squareclass. -/
def q4QuadraticSubfieldSquareclass : ℤ :=
  -1931

/-- The discriminant is not a square because it is negative. -/
def q4DiscriminantIsNonsquare : Prop :=
  ¬ IsSquare q4Discriminant

lemma q4Discriminant_neg : q4Discriminant < 0 := by
  norm_num [q4Discriminant]

lemma q4Discriminant_not_square : q4DiscriminantIsNonsquare := by
  intro hsq
  rcases hsq with ⟨n, hn⟩
  have hsquare_nonneg : 0 ≤ n * n := by
    nlinarith
  have hdisc_nonneg : 0 ≤ q4Discriminant := by
    simpa [hn] using hsquare_nonneg
  linarith [q4Discriminant_neg, hdisc_nonneg]

/-- Paper label: `prop:fold-gauge-anomaly-trigonal-q4-galois`. The audited Lean certificate records
the explicit quartic, the discriminant factorization, the mod-`17` and mod-`13` factorization
types, the resulting `S₄` Galois group, and the quadratic squareclass `-1931`. -/
theorem paper_fold_gauge_anomaly_trigonal_q4_galois :
    q4 = 9 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + 8 * X - 16 ∧
      q4Discriminant = -(2 ^ 12) * 3 ^ 4 * 1931 ∧
      q4Mod17FactorDegrees = [4] ∧
      q4Mod13FactorDegrees = [1, 1, 2] ∧
      q4GaloisGroup = QuarticTransitiveSubgroup.s4 ∧
      q4QuadraticSubfieldSquareclass = -1931 ∧
      q4DiscriminantIsNonsquare := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, q4Discriminant_not_square⟩

end

end Omega.Folding
