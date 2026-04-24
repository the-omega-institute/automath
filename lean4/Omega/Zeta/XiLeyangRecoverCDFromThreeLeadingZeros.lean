import Mathlib.Tactic
import Omega.Zeta.XiLeyangThreeLeadingZerosExtrapolateUcN6

namespace Omega.Zeta

namespace XiLeyangThreeLeadingZerosExtrapolateData

/-- The first two odd-square nodes `1` and `9`, viewed as elements of `Fin 3`. -/
def recoverNode (k : Fin 2) : Fin 3 :=
  ⟨k.1, Nat.lt_trans k.2 (by decide)⟩

/-- The two sample values used to recover the `n⁻²` and `n⁻⁴` coefficients. -/
def recoverSample (D : XiLeyangThreeLeadingZerosExtrapolateData) (k : Fin 2) (n : ℚ) : ℚ :=
  xiLeyangThreeLeadingExpansion D (recoverNode k) n

/-- The scaled discrepancy between the `k`th sample and the three-point extrapolated center. -/
def recoverB (D : XiLeyangThreeLeadingZerosExtrapolateData) (k : Fin 2) (n : ℚ) : ℚ :=
  n ^ 2 * (recoverSample D k n - xiLeyangThreeLeadingExtrapolate D n)

/-- The recovered `n⁻²` coefficient. -/
def recoveredSecondOrderCoeff (D : XiLeyangThreeLeadingZerosExtrapolateData) (n : ℚ) : ℚ :=
  (81 * recoverB D 0 n - recoverB D 1 n) / 72

/-- The recovered `n⁻⁴` coefficient. -/
def recoveredFourthOrderCoeff (D : XiLeyangThreeLeadingZerosExtrapolateData) (n : ℚ) : ℚ :=
  n ^ 2 * (recoverB D 1 n - 9 * recoverB D 0 n) / 72

/-- The surviving `n⁻⁴` tail in the recovered second-order coefficient. -/
def recoveredSecondOrderTail (D : XiLeyangThreeLeadingZerosExtrapolateData) (n : ℚ) : ℚ :=
  (81 * (D.sixthOrderCoeff (recoverNode 0) - xiLeyangThreeLeadingTailCombination D) -
      (D.sixthOrderCoeff (recoverNode 1) - xiLeyangThreeLeadingTailCombination D)) /
    (72 * n ^ 4)

/-- The surviving `n⁻²` tail in the recovered fourth-order coefficient. -/
def recoveredFourthOrderTail (D : XiLeyangThreeLeadingZerosExtrapolateData) (n : ℚ) : ℚ :=
  ((D.sixthOrderCoeff (recoverNode 1) - xiLeyangThreeLeadingTailCombination D) -
      9 * (D.sixthOrderCoeff (recoverNode 0) - xiLeyangThreeLeadingTailCombination D)) /
    (72 * n ^ 2)

/-- The two `B_k` linear combinations at nodes `1` and `9` recover the second- and fourth-order
coefficients up to the expected `n⁻⁴` and `n⁻²` tail terms. -/
def recoversSecondAndFourthOrderCoeffs (D : XiLeyangThreeLeadingZerosExtrapolateData) : Prop :=
  ∀ n : ℚ, n ≠ 0 →
    recoveredSecondOrderCoeff D n = D.secondOrderCoeff + recoveredSecondOrderTail D n ∧
      recoveredFourthOrderCoeff D n = D.fourthOrderCoeff + recoveredFourthOrderTail D n

end XiLeyangThreeLeadingZerosExtrapolateData

open XiLeyangThreeLeadingZerosExtrapolateData

/-- Paper label: `cor:xi-leyang-recover-C-D-from-three-leading-zeros`.
At the odd-square nodes `1` and `9`, the two `B_k` combinations give an exact `2 × 2` linear
system for the `n⁻²` and `n⁻⁴` coefficients, and the previously verified three-point
extrapolation isolates the remaining `n⁻⁴` and `n⁻²` tail terms. -/
theorem paper_xi_leyang_recover_C_D_from_three_leading_zeros
    (D : XiLeyangThreeLeadingZerosExtrapolateData) :
    D.recoversSecondAndFourthOrderCoeffs := by
  intro n hn
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have hn6 : n ^ 6 ≠ 0 := pow_ne_zero 6 hn
  have hcenter := paper_xi_leyang_three_leading_zeros_extrapolate_uc_n6 D n hn
  have h0 :
      recoverSample D 0 n =
        D.limitValue + D.secondOrderCoeff / n ^ 2 + D.fourthOrderCoeff / n ^ 4 +
          D.sixthOrderCoeff (recoverNode 0) / n ^ 6 := by
    simp [recoverSample, recoverNode, xiLeyangThreeLeadingExpansion, xiLeyangThreeLeadingNode]
  have h1 :
      recoverSample D 1 n =
        D.limitValue + 9 * D.secondOrderCoeff / n ^ 2 + 81 * D.fourthOrderCoeff / n ^ 4 +
          D.sixthOrderCoeff (recoverNode 1) / n ^ 6 := by
    simp [recoverSample, recoverNode, xiLeyangThreeLeadingExpansion, xiLeyangThreeLeadingNode]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [recoveredSecondOrderCoeff, recoveredSecondOrderTail, recoverB]
    simp [XiLeyangThreeLeadingZerosExtrapolateData.recoverB, hcenter, h0, h1]
    field_simp [hn2, hn4, hn6]
    ring_nf
  · rw [recoveredFourthOrderCoeff, recoveredFourthOrderTail, recoverB]
    simp [XiLeyangThreeLeadingZerosExtrapolateData.recoverB, hcenter, h0, h1]
    field_simp [hn2, hn4, hn6]
    ring_nf

end Omega.Zeta
