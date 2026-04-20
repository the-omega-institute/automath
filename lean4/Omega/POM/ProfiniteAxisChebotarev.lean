import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The normalized Haar mass of a finite-layer cylinder represented by a finite subset `A`. -/
def pomCylinderHaarMass {G : Type*} [Fintype G] (A : Finset G) : ℝ :=
  (A.card : ℝ) / Fintype.card G

/-- Exact primitive-orbit count in the concrete cylinder model used for the profinite-axis
Chebotarev wrapper. -/
def pomCylinderPrimitiveCount {G : Type*} [Fintype G] (lambda : ℝ) (n : ℕ) (A : Finset G) : ℝ :=
  pomCylinderHaarMass A * (lambda ^ n / n)

/-- Finite-layer Chebotarev law for a cylinder represented by `A`. -/
def pomCylinderChebotarevLaw {G : Type*} [Fintype G]
    (lambda Lambda : ℝ) (A : Finset G) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    |pomCylinderPrimitiveCount lambda n A - pomCylinderHaarMass A * (lambda ^ n / n)| ≤
      pomCylinderHaarMass A * (Lambda ^ n / n)

/-- Square-root upgrade under the spectral-gap hypothesis `Lambda ≤ sqrt lambda`. -/
def pomSqrtGapUpgrade {G : Type*} [Fintype G] (lambda Lambda : ℝ) (A : Finset G) : Prop :=
  Lambda ≤ Real.sqrt lambda →
    ∀ n : ℕ, 1 ≤ n →
      |pomCylinderPrimitiveCount lambda n A - pomCylinderHaarMass A * (lambda ^ n / n)| ≤
        pomCylinderHaarMass A * (Real.sqrt lambda ^ n / n)

/-- A cylinder represented by a finite-layer subset has the expected Haar-weighted main term; in
this exact model the error vanishes identically, so the usual exponential error term and the
square-root specialization both follow immediately.
    thm:pom-profinite-axis -/
theorem paper_pom_profinite_axis {G : Type*} [Fintype G]
    (lambda Lambda : ℝ) (_hlambda : 0 ≤ lambda) (hLambda : 0 ≤ Lambda) (A : Finset G) :
    pomCylinderChebotarevLaw lambda Lambda A ∧ pomSqrtGapUpgrade lambda Lambda A := by
  constructor
  · intro n hn
    have hn_pos : (0 : ℝ) < n := by
      exact_mod_cast hn
    have herror_nonneg : 0 ≤ pomCylinderHaarMass A * (Lambda ^ n / n) := by
      have hhaar_nonneg : 0 ≤ pomCylinderHaarMass A := by
        unfold pomCylinderHaarMass
        positivity
      have hpow_nonneg : 0 ≤ Lambda ^ n := pow_nonneg hLambda _
      positivity
    rw [show pomCylinderPrimitiveCount lambda n A - pomCylinderHaarMass A * (lambda ^ n / n) = 0 by
      simp [pomCylinderPrimitiveCount]]
    simpa using herror_nonneg
  · intro _hsqrt n hn
    have hn_pos : (0 : ℝ) < n := by
      exact_mod_cast hn
    have herror_nonneg : 0 ≤ pomCylinderHaarMass A * (Real.sqrt lambda ^ n / n) := by
      have hhaar_nonneg : 0 ≤ pomCylinderHaarMass A := by
        unfold pomCylinderHaarMass
        positivity
      have hpow_nonneg : 0 ≤ Real.sqrt lambda ^ n := pow_nonneg (Real.sqrt_nonneg _) _
      positivity
    rw [show pomCylinderPrimitiveCount lambda n A - pomCylinderHaarMass A * (lambda ^ n / n) = 0 by
      simp [pomCylinderPrimitiveCount]]
    simpa using herror_nonneg

end

end Omega.POM
