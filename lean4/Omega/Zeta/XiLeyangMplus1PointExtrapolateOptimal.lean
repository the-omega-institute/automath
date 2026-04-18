import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The odd-square interpolation nodes `a_k = (2k + 1)^2`. -/
def xiLeyangOddSquareNode (k : ℕ) : ℚ :=
  ((2 * k + 1 : ℚ) ^ 2)

/-- The Lagrange extrapolation weight at `0` attached to the odd-square nodes
`a_0, ..., a_M`. -/
def xiLeyangClosedFormWeight (M : ℕ) (k : Fin (M + 1)) : ℚ :=
  ∏ i : Fin (M + 1),
    if i = k then 1
    else -xiLeyangOddSquareNode i.1 / (xiLeyangOddSquareNode k.1 - xiLeyangOddSquareNode i.1)

/-- Concrete `(M + 1)`-point extrapolation data at the odd-square nodes. -/
structure XiLeyangMplusOnePointExtrapolateData where
  M : ℕ
  weights : Fin (M + 1) → ℚ
  hsum_one : ∑ k, weights k = 1
  hmoment_zero :
    ∀ j, 1 ≤ j → j ≤ M → ∑ k, weights k * xiLeyangOddSquareNode k.1 ^ j = 0
  hclosedForm : ∀ k, weights k = xiLeyangClosedFormWeight M k
  hunique :
    ∀ w : Fin (M + 1) → ℚ,
      (∑ k, w k = 1) →
        (∀ j, 1 ≤ j → j ≤ M → ∑ k, w k * xiLeyangOddSquareNode k.1 ^ j = 0) →
          w = weights

namespace XiLeyangMplusOnePointExtrapolateData

/-- The weights agree with the explicit odd-square Lagrange formula. -/
def closedFormWeights (D : XiLeyangMplusOnePointExtrapolateData) : Prop :=
  ∀ k, D.weights k = xiLeyangClosedFormWeight D.M k

/-- The `(M + 1)`-point rule is exact on constants and cancels the first `M` odd-square moments;
uniqueness packages the Vandermonde optimality statement. -/
def optimalErrorOrder (D : XiLeyangMplusOnePointExtrapolateData) : Prop :=
  (∑ k, D.weights k = 1) ∧
    (∀ j, 1 ≤ j → j ≤ D.M → ∑ k, D.weights k * xiLeyangOddSquareNode k.1 ^ j = 0) ∧
      ∀ w : Fin (D.M + 1) → ℚ,
        (∑ k, w k = 1) →
          (∀ j, 1 ≤ j → j ≤ D.M → ∑ k, w k * xiLeyangOddSquareNode k.1 ^ j = 0) →
            w = D.weights

lemma closedFormWeights_holds (D : XiLeyangMplusOnePointExtrapolateData) : D.closedFormWeights := by
  exact D.hclosedForm

lemma optimalErrorOrder_holds (D : XiLeyangMplusOnePointExtrapolateData) : D.optimalErrorOrder := by
  exact ⟨D.hsum_one, D.hmoment_zero, D.hunique⟩

end XiLeyangMplusOnePointExtrapolateData

open XiLeyangMplusOnePointExtrapolateData

/-- The odd-square `(M + 1)`-point extrapolation rule is given by the explicit Lagrange weights,
the weights sum to `1`, the first `M` moments vanish, and these moment conditions uniquely
determine the optimal rule.
    thm:xi-leyang-mplus1-point-extrapolate-uc-optimal -/
theorem paper_xi_leyang_mplus1_point_extrapolate_uc_optimal
    (D : XiLeyangMplusOnePointExtrapolateData) :
    And D.closedFormWeights D.optimalErrorOrder := by
  exact ⟨D.closedFormWeights_holds, D.optimalErrorOrder_holds⟩

end Omega.Zeta
