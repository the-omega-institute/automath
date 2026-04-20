import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The three odd-square nodes `a_k = (2k + 1)^2` for `k = 0, 1, 2`. -/
def xiLeyangThreeLeadingNode (k : Fin 3) : ℚ :=
  ((2 * (k : ℕ) + 1 : ℚ) ^ 2)

/-- The Vandermonde-cancellation weights solving the `3 × 3` odd-square system. -/
def xiLeyangThreeLeadingWeight (k : Fin 3) : ℚ :=
  if (k : ℕ) = 0 then 75 / 64 else if (k : ℕ) = 1 then -25 / 128 else 3 / 128

/-- Concrete three-point expansion data with explicit `n⁻²`, `n⁻⁴`, and `n⁻⁶` terms. -/
structure XiLeyangThreeLeadingZerosExtrapolateData where
  limitValue : ℚ
  secondOrderCoeff : ℚ
  fourthOrderCoeff : ℚ
  sixthOrderCoeff : Fin 3 → ℚ

/-- The three input expansions at the odd-square nodes. -/
def xiLeyangThreeLeadingExpansion
    (D : XiLeyangThreeLeadingZerosExtrapolateData) (k : Fin 3) (n : ℚ) : ℚ :=
  D.limitValue +
    D.secondOrderCoeff * xiLeyangThreeLeadingNode k / n ^ 2 +
    D.fourthOrderCoeff * xiLeyangThreeLeadingNode k ^ 2 / n ^ 4 +
    D.sixthOrderCoeff k / n ^ 6

/-- The weighted three-point extrapolation rule. -/
def xiLeyangThreeLeadingExtrapolate
    (D : XiLeyangThreeLeadingZerosExtrapolateData) (n : ℚ) : ℚ :=
  ∑ k, xiLeyangThreeLeadingWeight k * xiLeyangThreeLeadingExpansion D k n

/-- The surviving `n⁻⁶` coefficient after cancellation. -/
def xiLeyangThreeLeadingTailCombination (D : XiLeyangThreeLeadingZerosExtrapolateData) : ℚ :=
  ∑ k, xiLeyangThreeLeadingWeight k * D.sixthOrderCoeff k

/-- The extrapolation cancels the `n⁻²` and `n⁻⁴` terms and leaves an `O(n⁻⁶)` remainder. -/
def XiLeyangThreeLeadingZerosExtrapolateData.extrapolatesToOrderSix
    (D : XiLeyangThreeLeadingZerosExtrapolateData) : Prop :=
  ∀ n : ℚ, n ≠ 0 →
    xiLeyangThreeLeadingExtrapolate D n =
      D.limitValue + xiLeyangThreeLeadingTailCombination D / n ^ 6

lemma xiLeyangThreeLeading_weight_sum :
    (∑ k, xiLeyangThreeLeadingWeight k) = 1 := by
  rw [Fin.sum_univ_three]
  norm_num [xiLeyangThreeLeadingWeight]

lemma xiLeyangThreeLeading_first_moment :
    (∑ k, xiLeyangThreeLeadingWeight k * xiLeyangThreeLeadingNode k) = 0 := by
  rw [Fin.sum_univ_three]
  norm_num [xiLeyangThreeLeadingWeight, xiLeyangThreeLeadingNode]

lemma xiLeyangThreeLeading_second_moment :
    (∑ k, xiLeyangThreeLeadingWeight k * xiLeyangThreeLeadingNode k ^ 2) = 0 := by
  rw [Fin.sum_univ_three]
  norm_num [xiLeyangThreeLeadingWeight, xiLeyangThreeLeadingNode]

/-- Paper label: `thm:xi-leyang-three-leading-zeros-extrapolate-uc-n6`.
At the odd-square nodes `1, 9, 25`, the weights `75/64`, `-25/128`, and `3/128` sum to `1`
while the first two moments vanish, so substituting the three expansions leaves only the
`n⁻⁶` tail term. -/
theorem paper_xi_leyang_three_leading_zeros_extrapolate_uc_n6
    (D : XiLeyangThreeLeadingZerosExtrapolateData) : D.extrapolatesToOrderSix := by
  intro n hn
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have hn6 : n ^ 6 ≠ 0 := pow_ne_zero 6 hn
  rw [xiLeyangThreeLeadingExtrapolate, xiLeyangThreeLeadingTailCombination]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [xiLeyangThreeLeadingExpansion, xiLeyangThreeLeadingWeight, xiLeyangThreeLeadingNode]
  field_simp [hn2, hn4, hn6]
  ring

end Omega.Zeta
