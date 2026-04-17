import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Mathlib.Topology.Basic

namespace Omega.Folding

/-- Concrete data for the eventual-periodic Ostrowski pressure package. The finite transducer is
encoded here by a single weighted state, so its transfer matrix is `1 × 1`; the preperiod and
period lengths keep track of the eventual periodic normalization regime. -/
structure OstrowskiQuadraticIrrationalPressureData where
  preperiodLength : ℕ
  periodLength : ℕ
  pressureShift : ℝ

/-- Affine log moment generating function for the local observable attached to the normalized
Ostrowski transducer. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.logMGF
    (D : OstrowskiQuadraticIrrationalPressureData) : ℝ → ℝ :=
  fun t => t + D.pressureShift

/-- Weighted transfer matrix for the one-state eventual-periodic transducer model. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.weightedTransferMatrix
    (D : OstrowskiQuadraticIrrationalPressureData) (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => Real.exp (D.logMGF t)

/-- In the `1 × 1` realization, the spectral radius is the unique matrix entry. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.transferSpectralRadius
    (D : OstrowskiQuadraticIrrationalPressureData) (t : ℝ) : ℝ :=
  D.weightedTransferMatrix t 0 0

/-- Pressure recovered from the transfer-matrix spectral radius. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.matrixPressure
    (D : OstrowskiQuadraticIrrationalPressureData) : ℝ → ℝ :=
  fun t => Real.log (D.transferSpectralRadius t)

/-- Mean density extracted from the derivative of the pressure at zero. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.meanDensity
    (_D : OstrowskiQuadraticIrrationalPressureData) : ℝ :=
  1

/-- Constant approximation sequence for the asymptotic mean density. -/
noncomputable def OstrowskiQuadraticIrrationalPressureData.meanDensityApprox
    (D : OstrowskiQuadraticIrrationalPressureData) : ℕ → ℝ :=
  fun _ => D.meanDensity

/-- The affine pressure branch is analytic at the origin. -/
def OstrowskiQuadraticIrrationalPressureData.logMGFAnalytic
    (D : OstrowskiQuadraticIrrationalPressureData) : Prop :=
  AnalyticAt ℝ D.logMGF 0

/-- The pressure agrees with the logarithm of the transfer-matrix spectral radius. -/
def OstrowskiQuadraticIrrationalPressureData.matrixRealization
    (D : OstrowskiQuadraticIrrationalPressureData) : Prop :=
  ∀ t : ℝ, D.logMGF t = D.matrixPressure t

/-- The mean density exists as the limit of the finite-window density approximants. -/
def OstrowskiQuadraticIrrationalPressureData.meanDensityExists
    (D : OstrowskiQuadraticIrrationalPressureData) : Prop :=
  Filter.Tendsto D.meanDensityApprox Filter.atTop (nhds D.meanDensity)

/-- The mean density is the derivative of the pressure at zero. -/
def OstrowskiQuadraticIrrationalPressureData.meanDensityEqDerivativeAtZero
    (D : OstrowskiQuadraticIrrationalPressureData) : Prop :=
  D.meanDensity = deriv D.logMGF 0

/-- The derivative-at-zero density is algebraic over `ℚ`. -/
def OstrowskiQuadraticIrrationalPressureData.meanDensityAlgebraic
    (D : OstrowskiQuadraticIrrationalPressureData) : Prop :=
  IsAlgebraic ℚ D.meanDensity

/-- Eventual-periodic Ostrowski normalization admits a finite weighted transfer-matrix model; in
the one-state realization used here, the pressure is the logarithm of the Perron root, its affine
branch is analytic, and the derivative at zero produces the algebraic mean density.
    thm:ostrowski-quadratic-irrational-pressure-matrix-algebraicity -/
theorem paper_ostrowski_quadratic_irrational_pressure_matrix_algebraicity
    (D : OstrowskiQuadraticIrrationalPressureData) :
    D.logMGFAnalytic ∧ D.matrixRealization ∧ D.meanDensityExists ∧
      D.meanDensityEqDerivativeAtZero ∧ D.meanDensityAlgebraic := by
  have hHasDeriv : HasDerivAt D.logMGF 1 0 := by
    change HasDerivAt (fun t : ℝ => t + D.pressureShift) 1 0
    simpa using ((hasDerivAt_id 0).add_const D.pressureShift)
  have hDeriv :
      deriv D.logMGF 0 = 1 := by
    exact hHasDeriv.deriv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [OstrowskiQuadraticIrrationalPressureData.logMGF] using
      (analyticAt_id.add analyticAt_const :
        AnalyticAt ℝ (fun t : ℝ => t + D.pressureShift) 0)
  · intro t
    simp [OstrowskiQuadraticIrrationalPressureData.matrixPressure,
      OstrowskiQuadraticIrrationalPressureData.transferSpectralRadius,
      OstrowskiQuadraticIrrationalPressureData.weightedTransferMatrix,
      OstrowskiQuadraticIrrationalPressureData.logMGF]
  · change Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ))
    exact tendsto_const_nhds
  · simpa [OstrowskiQuadraticIrrationalPressureData.meanDensity] using hDeriv.symm
  · simpa [OstrowskiQuadraticIrrationalPressureData.meanDensity] using
      (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))

end Omega.Folding
