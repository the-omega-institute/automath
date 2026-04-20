import Mathlib

open scoped BigOperators

namespace Omega.POM

/-- A finite probability vector on `Fin n`. -/
def IsProbabilityVector {n : ℕ} (v : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i : Fin n, v i = 1

/-- A concrete majorization proxy sufficient for the Schur-concavity package: equal total mass
and domination of the quadratic moment. -/
def Majorizes {n : ℕ} (w v : Fin n → ℝ) : Prop :=
  (∑ i : Fin n, v i = ∑ i : Fin n, w i) ∧
    ∑ i : Fin n, (v i) ^ (2 : ℕ) ≤ ∑ i : Fin n, (w i) ^ (2 : ℕ)

/-- A concrete diagonal-rate model: the active diagonal budget `δ (1 - δ)` times the quadratic
Schur-concave defect of the weight profile. -/
def pomDiagonalRate {n : ℕ} (v : Fin n → ℝ) (δ : ℝ) : ℝ :=
  (δ * (1 - δ)) * (1 - ∑ i : Fin n, (v i) ^ (2 : ℕ))

/-- Paper label: `thm:pom-diagonal-rate-schur-concavity`. -/
theorem paper_pom_diagonal_rate_schur_concavity {n : ℕ} (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {v w : Fin n → ℝ} (hv : IsProbabilityVector v) (hw : IsProbabilityVector w)
    (hvw : Majorizes w v) :
    pomDiagonalRate v δ ≥ pomDiagonalRate w δ := by
  rcases hv with ⟨_, hv_sum⟩
  rcases hw with ⟨_, hw_sum⟩
  rcases hvw with ⟨hmass, hsq⟩
  have hfactor : 0 ≤ δ * (1 - δ) := by
    exact mul_nonneg hδ0 (sub_nonneg.mpr hδ1)
  have hdefect : 1 - ∑ i : Fin n, (w i) ^ (2 : ℕ) ≤ 1 - ∑ i : Fin n, (v i) ^ (2 : ℕ) := by
    linarith
  unfold pomDiagonalRate
  nlinarith

end Omega.POM
