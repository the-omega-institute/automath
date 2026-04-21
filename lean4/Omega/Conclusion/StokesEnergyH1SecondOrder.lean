import Mathlib
import Omega.Conclusion.StokesEnergyDyadicMartingale

namespace Omega.Conclusion

open scoped BigOperators

/-- The dyadic second-order decay rate `2^{-2m}` written as `(1/4)^m`. -/
noncomputable def dyadicSecondOrderRate (m : ℕ) : ℝ :=
  ((1 : ℝ) / 4) ^ m

/-- The cellwise second-order error extracted from the dyadic martingale energy increment. -/
noncomputable def localSecondOrderError (M : DyadicMartingale) : ℝ :=
  (M.left ^ 2 + M.right ^ 2) / 2 - M.parent ^ 2

/-- Finite dyadic package for the second-order `H¹` Stokes-energy estimate. The local error is the
martingale increment on each dyadic cell, and the cellwise Poincare bound compares it to the local
`H¹` mass times the dyadic rate `2^{-2m}`. -/
structure StokesEnergyH1SecondOrderData where
  m : ℕ
  cellCount : ℕ
  martingale : Fin cellCount → DyadicMartingale
  cellH1 : Fin cellCount → ℝ
  totalH1 : ℝ
  totalH1_eq : totalH1 = ∑ Q : Fin cellCount, cellH1 Q
  cellH1_nonneg : ∀ Q : Fin cellCount, 0 ≤ cellH1 Q
  poincare_cell :
    ∀ Q : Fin cellCount,
      ((martingale Q).left - (martingale Q).right) ^ 2 / 4 ≤
        cellH1 Q * dyadicSecondOrderRate m

namespace StokesEnergyH1SecondOrderData

/-- Global second-order error obtained by summing the cellwise martingale increments. -/
noncomputable def globalSecondOrderError (D : StokesEnergyH1SecondOrderData) : ℝ :=
  ∑ Q : Fin D.cellCount, localSecondOrderError (D.martingale Q)

/-- The package-level `O(2^{-2m})` error bound in terms of the total `H¹` mass. -/
def HasSecondOrderErrorBound (D : StokesEnergyH1SecondOrderData) : Prop :=
  D.globalSecondOrderError ≤ D.totalH1 * dyadicSecondOrderRate D.m

end StokesEnergyH1SecondOrderData

/-- Paper label: `cor:conclusion-stokes-energy-h1-second-order`. Summing the dyadic martingale
increments cellwise and applying the cubewise Poincare bounds yields the global
`O(2^{-2m})` estimate. -/
theorem paper_conclusion_stokes_energy_h1_second_order (D : StokesEnergyH1SecondOrderData) :
    D.HasSecondOrderErrorBound := by
  unfold StokesEnergyH1SecondOrderData.HasSecondOrderErrorBound
  unfold StokesEnergyH1SecondOrderData.globalSecondOrderError
  have hlocal :
      ∀ Q : Fin D.cellCount,
        localSecondOrderError (D.martingale Q) =
          ((D.martingale Q).left - (D.martingale Q).right) ^ 2 / 4 := by
    intro Q
    have hinc := (paper_conclusion_stokes_energy_dyadic_martingale (D.martingale Q)).2.2
    simpa [localSecondOrderError] using hinc
  have hsum :
      ∑ Q : Fin D.cellCount, localSecondOrderError (D.martingale Q) ≤
        ∑ Q : Fin D.cellCount, D.cellH1 Q * dyadicSecondOrderRate D.m := by
    refine Finset.sum_le_sum ?_
    intro Q hQ
    rw [hlocal Q]
    exact D.poincare_cell Q
  calc
    ∑ Q : Fin D.cellCount, localSecondOrderError (D.martingale Q)
        ≤ ∑ Q : Fin D.cellCount, D.cellH1 Q * dyadicSecondOrderRate D.m := hsum
    _ = (∑ Q : Fin D.cellCount, D.cellH1 Q) * dyadicSecondOrderRate D.m := by
          rw [Finset.sum_mul]
    _ = D.totalH1 * dyadicSecondOrderRate D.m := by
          rw [← D.totalH1_eq]

end Omega.Conclusion
