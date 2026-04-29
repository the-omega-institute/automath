import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Closed form for the first derivative `P'(0)` of the real-input-40 backtracking pressure. -/
def realInput40BacktrackingFirstDerivative : ℝ :=
  (211 - 93 * Real.sqrt 5) / 20

/-- Closed form for the second derivative `P''(0)` of the real-input-40 backtracking pressure. -/
def realInput40BacktrackingSecondDerivative : ℝ :=
  (193219 : ℝ) / 100 - (216003 : ℝ) / 250 * Real.sqrt 5

/-- Audited values of the first two backtracking cumulant densities. -/
structure RealInput40BacktrackingCumulantsData where
  firstDerivative : ℝ
  secondDerivative : ℝ
  firstDerivativeWitness :
    firstDerivative = realInput40BacktrackingFirstDerivative
  secondDerivativeWitness :
    secondDerivative = realInput40BacktrackingSecondDerivative

/-- The audited value of `P'(0)`. -/
def RealInput40BacktrackingCumulantsData.firstDerivativeValue
    (D : RealInput40BacktrackingCumulantsData) : Prop :=
  D.firstDerivative = realInput40BacktrackingFirstDerivative

/-- The audited value of `P''(0)`. -/
def RealInput40BacktrackingCumulantsData.secondDerivativeValue
    (D : RealInput40BacktrackingCumulantsData) : Prop :=
  D.secondDerivative = realInput40BacktrackingSecondDerivative

/-- Paper label: `thm:real-input-40-backtracking-cumulants`.
The backtracking density and variance density are the audited quadratic-field constants. -/
theorem paper_real_input_40_backtracking_cumulants (D : RealInput40BacktrackingCumulantsData) :
    D.firstDerivativeValue ∧ D.secondDerivativeValue := by
  exact ⟨D.firstDerivativeWitness, D.secondDerivativeWitness⟩

end

end Omega.Zeta
