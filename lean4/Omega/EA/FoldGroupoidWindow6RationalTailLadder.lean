import Mathlib.Tactic
import Omega.Folding.Window6

namespace Omega.EA

open Polynomial

noncomputable section

/-- The three odd sphere degrees in the window-`6` rational tail ladder. -/
inductive Window6RationalTailDegree where
  | d3
  | d5
  | d7
  deriving DecidableEq, Repr

/-- Tail multiplicities specialized to the audited window-`6` histogram `2:8, 3:4, 4:9`. -/
def window6RationalTailCount : Window6RationalTailDegree → ℕ
  | .d3 => cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4
  | .d5 => cBinFiberHist 6 3 + cBinFiberHist 6 4
  | .d7 => cBinFiberHist 6 4

/-- The exterior-algebra Poincare polynomial attached to the window-`6` rational tail ladder. -/
def window6RationalTailPoincarePolynomial : Polynomial ℤ :=
  (((1 : ℤ[X]) + Polynomial.X ^ 3) ^ window6RationalTailCount .d3) *
    (((1 : ℤ[X]) + Polynomial.X ^ 5) ^ window6RationalTailCount .d5) *
      (((1 : ℤ[X]) + Polynomial.X ^ 7) ^ window6RationalTailCount .d7)

/-- Rational-homotopy product data specialized to the three audited odd sphere degrees. -/
def window6RationalHomotopyDecomposition : Prop :=
  window6RationalTailCount .d3 = 21 ∧
    window6RationalTailCount .d5 = 13 ∧
    window6RationalTailCount .d7 = 9

/-- Exterior-algebra cohomology data for the same three odd-degree generators. -/
def window6CohomologyExteriorAlgebra : Prop :=
  window6RationalTailCount .d3 = 21 ∧
    window6RationalTailCount .d5 = 13 ∧
    window6RationalTailCount .d7 = 9

/-- Closed-form Poincare polynomial of the specialized ladder. -/
def window6PoincarePolynomialClosedForm : Prop :=
  window6RationalTailPoincarePolynomial =
    (((1 : ℤ[X]) + Polynomial.X ^ 3) ^ 21) *
      (((1 : ℤ[X]) + Polynomial.X ^ 5) ^ 13) *
        (((1 : ℤ[X]) + Polynomial.X ^ 7) ^ 9)

private lemma window6_rational_tail_counts :
    window6RationalHomotopyDecomposition := by
  rcases Omega.invariant_ring_from_histogram with ⟨h21, h13, h9⟩
  exact ⟨h21, h13, h9⟩

private lemma window6_cohomology_exterior_algebra :
    window6CohomologyExteriorAlgebra := by
  exact window6_rational_tail_counts

private lemma window6_poincare_closed_form :
    window6PoincarePolynomialClosedForm := by
  rcases window6_rational_tail_counts with ⟨h21, h13, h9⟩
  unfold window6PoincarePolynomialClosedForm window6RationalTailPoincarePolynomial
  rw [h21, h13, h9]

/-- Paper label: `cor:fold-groupoid-window6-rational-tail-ladder`.
For `m = 6`, the audited tail counts are `21, 13, 9`, yielding the odd-sphere ladder, the
matching exterior-algebra generator counts, and the closed Poincare polynomial. -/
theorem paper_fold_groupoid_window6_rational_tail_ladder :
    window6RationalHomotopyDecomposition ∧
      window6CohomologyExteriorAlgebra ∧
      window6PoincarePolynomialClosedForm := by
  exact ⟨window6_rational_tail_counts, window6_cohomology_exterior_algebra,
    window6_poincare_closed_form⟩

end

end Omega.EA
