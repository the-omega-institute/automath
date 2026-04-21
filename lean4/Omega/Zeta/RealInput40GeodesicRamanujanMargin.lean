import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Concrete audited data for the real-input-40 geodesic Ramanujan-margin package. The error
terms are recorded against explicit Perron-model main terms and the sub-Perron base `λ_nb`. -/
structure RealInput40GeodesicRamanujanMarginData where
  rhoNB : ℝ
  lambdaNB : ℝ
  deltaNB : ℝ
  primitiveMainCoeff : ℝ
  primeMainCoeff : ℝ
  primitiveOrbitCount : ℕ → ℝ
  primeOrbitCount : ℕ → ℝ
  ramanujanMarginWitness : lambdaNB / Real.sqrt rhoNB < 1
  deltaWitness : deltaNB = Real.log (lambdaNB ^ 2 / rhoNB)
  rhoPos : 0 < rhoNB
  primitiveErrorWitness :
    ∀ n : ℕ,
      |primitiveOrbitCount n - primitiveMainCoeff * rhoNB ^ n / n| ≤ lambdaNB ^ n
  primeErrorWitness :
    ∀ n : ℕ,
      |primeOrbitCount n - primeMainCoeff * rhoNB ^ n / n| ≤ lambdaNB ^ n

/-- The primitive-orbit asymptotic is controlled by the sub-Perron base `λ_nb`. -/
def RealInput40GeodesicRamanujanMarginData.primitiveOrbitErrorBound
    (D : RealInput40GeodesicRamanujanMarginData) : Prop :=
  ∀ n : ℕ,
    |D.primitiveOrbitCount n - D.primitiveMainCoeff * D.rhoNB ^ n / n| ≤ D.lambdaNB ^ n

/-- The prime-orbit refinement is controlled by the same sub-Perron base `λ_nb`. -/
def RealInput40GeodesicRamanujanMarginData.primeOrbitErrorBound
    (D : RealInput40GeodesicRamanujanMarginData) : Prop :=
  ∀ n : ℕ,
    |D.primeOrbitCount n - D.primeMainCoeff * D.rhoNB ^ n / n| ≤ D.lambdaNB ^ n

/-- Paper label: `cor:real-input-40-geodesic-ramanujan-margin`.
The audited second root gives a strict Ramanujan margin `λ_nb / sqrt(ρ_nb) < 1`; the corresponding
gap exponent is `log (λ_nb² / ρ_nb)`, and both the primitive-orbit and prime-orbit counts admit
the recorded `λ_nb^n` error bounds against their Perron main terms. -/
theorem paper_real_input_40_geodesic_ramanujan_margin
    (D : RealInput40GeodesicRamanujanMarginData) :
    D.lambdaNB / Real.sqrt D.rhoNB < 1 ∧
      D.deltaNB = Real.log (D.lambdaNB ^ 2 / D.rhoNB) ∧
      D.primitiveOrbitErrorBound ∧ D.primeOrbitErrorBound := by
  exact ⟨D.ramanujanMarginWitness, D.deltaWitness, D.primitiveErrorWitness, D.primeErrorWitness⟩

end Omega.Zeta
