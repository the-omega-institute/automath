import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete single-branch projective-pressure datum used to certify the Hölder/log-convexity
claim at the interpolation point between `q₀` and `q₁`. The Perron eigenfunction is the constant
function `1`, so the Hölder step is pointwise and exact. -/
structure ProjectivePressureHolderData where
  weight : ℝ
  outputAlphabetCard : ℕ
  q0 : ℝ
  q1 : ℝ
  theta : ℝ
  hweight : 0 < weight
  hcard : 0 < outputAlphabetCard
  htheta_nonneg : 0 ≤ theta
  htheta_le_one : theta ≤ 1

/-- The interpolated exponent `q_θ = (1-θ) q₀ + θ q₁`. -/
def ProjectivePressureHolderData.qTheta (D : ProjectivePressureHolderData) : ℝ :=
  (1 - D.theta) * D.q0 + D.theta * D.q1

/-- In the one-branch model the transfer operator just multiplies by the branch weight `g^q`. -/
noncomputable def ProjectivePressureHolderData.transfer
    (D : ProjectivePressureHolderData) (q x : ℝ) : ℝ :=
  D.weight ^ q * x

/-- The Perron eigenfunction is the constant positive function `1`. -/
noncomputable def ProjectivePressureHolderData.eigenfunction
    (_D : ProjectivePressureHolderData) (_q : ℝ) : ℝ :=
  1

/-- The corresponding Perron eigenvalue. -/
noncomputable def ProjectivePressureHolderData.lambda
    (D : ProjectivePressureHolderData) (q : ℝ) : ℝ :=
  D.weight ^ q

/-- The Hölder interpolant `h_{q₀}^{1-θ} h_{q₁}^θ`. -/
noncomputable def ProjectivePressureHolderData.holderInterpolant
    (D : ProjectivePressureHolderData) : ℝ :=
  D.eigenfunction D.q0 ^ (1 - D.theta) * D.eigenfunction D.q1 ^ D.theta

/-- The normalized free energy `Λ(t) = log (λ(t+1) / |A_out|)`. -/
noncomputable def ProjectivePressureHolderData.Lambda
    (D : ProjectivePressureHolderData) (t : ℝ) : ℝ :=
  Real.log (D.lambda (t + 1) / D.outputAlphabetCard)

/-- The pointwise Hölder step for the interpolated eigenfunction. -/
def ProjectivePressureHolderData.holderStep (D : ProjectivePressureHolderData) : Prop :=
  D.transfer D.qTheta D.holderInterpolant ≤
    (D.lambda D.q0 ^ (1 - D.theta) * D.lambda D.q1 ^ D.theta) * D.holderInterpolant

/-- Log-convexity of `q ↦ λ(q)` at the chosen interpolation point. -/
def ProjectivePressureHolderData.lambdaLogConvex (D : ProjectivePressureHolderData) : Prop :=
  D.lambda D.qTheta ≤ D.lambda D.q0 ^ (1 - D.theta) * D.lambda D.q1 ^ D.theta

/-- The affine interpolation points for the shifted variable `t = q - 1`. -/
def ProjectivePressureHolderData.t0 (D : ProjectivePressureHolderData) : ℝ := D.q0 - 1

/-- The affine interpolation points for the shifted variable `t = q - 1`. -/
def ProjectivePressureHolderData.t1 (D : ProjectivePressureHolderData) : ℝ := D.q1 - 1

/-- The affine interpolation points for the shifted variable `t = q - 1`. -/
def ProjectivePressureHolderData.tTheta (D : ProjectivePressureHolderData) : ℝ :=
  (1 - D.theta) * D.t0 + D.theta * D.t1

/-- Convexity of `Λ` at the same interpolation point. -/
def ProjectivePressureHolderData.LambdaConvex (D : ProjectivePressureHolderData) : Prop :=
  D.Lambda D.tTheta ≤ (1 - D.theta) * D.Lambda D.t0 + D.theta * D.Lambda D.t1

/-- Combined Holder step, log-convexity of the Perron root, and convexity of the normalized free
energy. -/
def ProjectivePressureHolderData.logConvexPressure (D : ProjectivePressureHolderData) : Prop :=
  D.holderStep ∧ D.lambdaLogConvex ∧ D.LambdaConvex

private lemma qTheta_eq_add (D : ProjectivePressureHolderData) :
    D.qTheta = (1 - D.theta) * D.q0 + D.theta * D.q1 := rfl

private lemma lambda_qTheta_eq (D : ProjectivePressureHolderData) :
    D.lambda D.qTheta = D.lambda D.q0 ^ (1 - D.theta) * D.lambda D.q1 ^ D.theta := by
  rw [ProjectivePressureHolderData.lambda, ProjectivePressureHolderData.lambda,
    ProjectivePressureHolderData.lambda, qTheta_eq_add, Real.rpow_add D.hweight]
  rw [mul_comm (1 - D.theta) D.q0, mul_comm D.theta D.q1]
  rw [← Real.rpow_mul D.hweight.le D.q0 (1 - D.theta)]
  rw [← Real.rpow_mul D.hweight.le D.q1 D.theta]

private lemma holderInterpolant_eq_one (D : ProjectivePressureHolderData) :
    D.holderInterpolant = 1 := by
  simp [ProjectivePressureHolderData.holderInterpolant,
    ProjectivePressureHolderData.eigenfunction]

private lemma Lambda_eq_affine (D : ProjectivePressureHolderData) (t : ℝ) :
    D.Lambda t = (t + 1) * Real.log D.weight - Real.log D.outputAlphabetCard := by
  rw [ProjectivePressureHolderData.Lambda, ProjectivePressureHolderData.lambda,
    Real.log_div (Real.rpow_pos_of_pos D.hweight _).ne'
      (by exact_mod_cast Nat.ne_of_gt D.hcard)]
  rw [Real.log_rpow D.hweight]

private lemma tTheta_add_one_eq_qTheta (D : ProjectivePressureHolderData) :
    D.tTheta + 1 = D.qTheta := by
  simp [ProjectivePressureHolderData.tTheta, ProjectivePressureHolderData.t0,
    ProjectivePressureHolderData.t1, ProjectivePressureHolderData.qTheta]
  ring

/-- Packaging the single-branch Perron eigenfunction hypotheses, the pointwise Hölder estimate,
the resulting log-convexity of `λ`, and the induced convexity of `Λ`.
    thm:pom-projective-pressure-holder-logconvex -/
theorem paper_pom_projective_pressure_holder_logconvex
    (D : ProjectivePressureHolderData) : D.logConvexPressure := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ProjectivePressureHolderData.holderStep, ProjectivePressureHolderData.transfer,
      holderInterpolant_eq_one] using le_of_eq (lambda_qTheta_eq D)
  · rw [ProjectivePressureHolderData.lambdaLogConvex]
    exact le_of_eq (lambda_qTheta_eq D)
  · rw [ProjectivePressureHolderData.LambdaConvex]
    apply le_of_eq
    rw [Lambda_eq_affine D D.tTheta, Lambda_eq_affine D D.t0, Lambda_eq_affine D D.t1]
    simp [ProjectivePressureHolderData.tTheta]
    ring

end Omega.POM
