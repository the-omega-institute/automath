import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The distortion threshold for binary marginals `w(0) = p`, `w(1) = 1 - p`. -/
def binaryDiagonalThreshold (p : ℝ) : ℝ :=
  2 * p * (1 - p)

/-- The boundary parameter forced by the diagonal constraint `P(X = Y) = 1 - δ`. -/
def binaryBoundaryParam (p δ : ℝ) : ℝ :=
  p - δ / 2

/-- The parameter corresponding to the independent coupling. -/
def binaryIndependentParam (p : ℝ) : ℝ :=
  p ^ 2

/-- The one-parameter family of binary couplings with marginals `(p, 1 - p)`. -/
def binaryCoupling (p a : ℝ) : Bool → Bool → ℝ
  | false, false => a
  | false, true => p - a
  | true, false => p - a
  | true, true => 1 - 2 * p + a

/-- Diagonal mass of the coupling `P(a)`. -/
def binaryDiagonalMass (p a : ℝ) : ℝ :=
  binaryCoupling p a false false + binaryCoupling p a true true

/-- The scalar KL objective attached to the binary coupling family. -/
noncomputable def binaryScalarKL (p a : ℝ) : ℝ :=
  a * Real.log (a / (p ^ 2)) +
    (p - a) * Real.log ((p - a) / (p * (1 - p))) +
      (p - a) * Real.log ((p - a) / (p * (1 - p))) +
        (1 - 2 * p + a) * Real.log ((1 - 2 * p + a) / ((1 - p) ^ 2))

/-- The formal second derivative of the scalar KL objective on the binary feasible interval. -/
def binaryScalarSecondDerivative (p a : ℝ) : ℝ :=
  1 / a + 2 / (p - a) + 1 / (1 - 2 * p + a)

/-- Concrete binary closed-form package used by the paper-facing theorem. It records the boundary
parameterization, the independence threshold, the explicit scalar KL reduction, and positivity of
the second derivative on the interior feasible region. -/
def pomDiagonalRateBinaryClosedForm : Prop :=
  ∀ ⦃p δ : ℝ⦄, 0 < p → p < 1 → 0 ≤ δ → δ ≤ 1 →
    let δ0 := binaryDiagonalThreshold p
    let a := binaryBoundaryParam p δ
    let ai := binaryIndependentParam p
    (δ ≤ δ0 → 0 ≤ a ∧ a ≤ p ∧ 0 ≤ binaryCoupling p a true true) ∧
      binaryCoupling p a false true = δ / 2 ∧
      binaryCoupling p a true false = δ / 2 ∧
      binaryCoupling p a true true = (1 - p) - δ / 2 ∧
      binaryDiagonalMass p a = 1 - δ ∧
      (δ0 ≤ δ ↔ a ≤ ai) ∧
      (δ < δ0 → ai < a) ∧
      binaryScalarKL p a =
        (p - δ / 2) * Real.log ((p - δ / 2) / (p ^ 2)) +
          ((1 - p) - δ / 2) * Real.log (((1 - p) - δ / 2) / ((1 - p) ^ 2)) +
            δ * Real.log ((δ / 2) / (p * (1 - p))) ∧
      (δ0 ≤ δ → binaryScalarKL p ai = 0) ∧
      (∀ a' : ℝ, 0 < a' → a' < p → 2 * p - 1 < a' → 0 < binaryScalarSecondDerivative p a')

/-- Binary closed form: the diagonal constraint fixes the unique boundary parameter
`a = p - δ / 2`, independence is feasible exactly when `δ ≥ δ₀ = 2p(1-p)`, the KL objective
reduces to the explicit scalar expression, and its second derivative is strictly positive on the
interior feasible interval.
    thm:pom-diagonal-rate-binary-closed-form -/
theorem paper_pom_diagonal_rate_binary_closed_form : pomDiagonalRateBinaryClosedForm := by
  intro p δ hp0 hp1 hδ0 hδ1
  dsimp [binaryDiagonalThreshold, binaryBoundaryParam, binaryIndependentParam]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hδ_le
    refine ⟨?_, by linarith, ?_⟩
    · nlinarith
    · show 0 ≤ 1 - 2 * p + (p - δ / 2)
      nlinarith
  · simp [binaryCoupling]
  · simp [binaryCoupling]
  · simp [binaryCoupling]
    ring
  · unfold binaryDiagonalMass binaryCoupling
    ring
  · constructor <;> intro h
    · nlinarith
    · nlinarith
  · intro hlt
    nlinarith
  · unfold binaryScalarKL
    have hDiag : 1 - 2 * p + (p - δ / 2) = (1 - p) - δ / 2 := by ring
    rw [hDiag]
    ring_nf
  · intro hge
    unfold binaryScalarKL
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    have hp1_ne : 1 - p ≠ 0 := by linarith
    have hpmix_ne : p * (1 - p) ≠ 0 := mul_ne_zero hp_ne hp1_ne
    rw [show p - p ^ 2 = p * (1 - p) by ring]
    rw [show 1 - 2 * p + p ^ 2 = (1 - p) ^ 2 by ring]
    simp [hp_ne, hp1_ne, hpmix_ne]
  · intro a' ha'0 ha'p ha'low
    unfold binaryScalarSecondDerivative
    have hpa : 0 < p - a' := sub_pos.mpr ha'p
    have hdiag : 0 < 1 - 2 * p + a' := by linarith
    have h1 : 0 < 1 / a' := one_div_pos.mpr ha'0
    have h2 : 0 < 2 / (p - a') := div_pos (by norm_num) hpa
    have h3 : 0 < 1 / (1 - 2 * p + a') := one_div_pos.mpr hdiag
    linarith

end

end Omega.POM
