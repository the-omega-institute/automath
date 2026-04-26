import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- The secant line between the endpoint pressures `τ₀` and `τ₁`. -/
def derived_projective_pressure_secant_rigidity_secant (τ₀ τ₁ θ : ℝ) : ℝ :=
  (1 - θ) * τ₀ + θ * τ₁

/-- A concrete convex pressure profile with endpoint values `τ₀`, `τ₁` and a nonnegative convex
correction `c * θ * (θ - 1)`. -/
def derived_projective_pressure_secant_rigidity_pressure (τ₀ τ₁ c θ : ℝ) : ℝ :=
  derived_projective_pressure_secant_rigidity_secant τ₀ τ₁ θ + c * θ * (θ - 1)

/-- Integer-anchor exponential profile attached to the pressure interpolation. -/
noncomputable def derived_projective_pressure_secant_rigidity_radius
    (tau0 tau1 c : ℝ) (N n : ℕ) : ℝ :=
  Real.exp
    (derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c ((n : ℝ) / N))

/-- Equality with the endpoint secant at one interior point forces the convex correction to vanish,
and then every integer anchor lies on the geometric interpolation between the two endpoint
pressures. -/
def derived_projective_pressure_secant_rigidity_statement : Prop :=
  ∀ tau0 tau1 c thetaStar : ℝ, 0 ≤ c → 0 < thetaStar → thetaStar < 1 →
    derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c thetaStar =
      derived_projective_pressure_secant_rigidity_secant tau0 tau1 thetaStar →
        (∀ theta : ℝ,
          derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c theta =
            derived_projective_pressure_secant_rigidity_secant tau0 tau1 theta) ∧
        (∀ N m n : ℕ, 0 < m → m < N →
          derived_projective_pressure_secant_rigidity_radius tau0 tau1 c N n =
            Real.exp ((1 - (n : ℝ) / N) * tau0) * Real.exp (((n : ℝ) / N) * tau1))

lemma derived_projective_pressure_secant_rigidity_correction_vanishes
    {tau0 tau1 c thetaStar : ℝ} (_hc : 0 ≤ c) (hTheta0 : 0 < thetaStar) (hTheta1 : thetaStar < 1)
    (heq :
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c thetaStar =
        derived_projective_pressure_secant_rigidity_secant tau0 tau1 thetaStar) :
    c = 0 := by
  dsimp [derived_projective_pressure_secant_rigidity_pressure,
    derived_projective_pressure_secant_rigidity_secant] at heq
  have hprod : c * thetaStar * (thetaStar - 1) = 0 := by
    nlinarith [heq]
  have hThetaNe : thetaStar ≠ 0 := by linarith
  have hThetaSubNe : thetaStar - 1 ≠ 0 := by linarith
  have hprod' : (c * thetaStar) * (thetaStar - 1) = 0 := by
    simpa [mul_assoc] using hprod
  have hMul : c * thetaStar = 0 := (mul_eq_zero.mp hprod').resolve_right hThetaSubNe
  exact (mul_eq_zero.mp hMul).resolve_right hThetaNe

lemma derived_projective_pressure_secant_rigidity_all_points
    {tau0 tau1 c thetaStar : ℝ} (hc : 0 ≤ c) (hTheta0 : 0 < thetaStar)
    (hTheta1 : thetaStar < 1)
    (heq :
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c thetaStar =
        derived_projective_pressure_secant_rigidity_secant tau0 tau1 thetaStar) :
    ∀ theta : ℝ,
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c theta =
        derived_projective_pressure_secant_rigidity_secant tau0 tau1 theta := by
  have hc0 :
      c = 0 :=
    derived_projective_pressure_secant_rigidity_correction_vanishes hc hTheta0 hTheta1 heq
  intro theta
  simp [derived_projective_pressure_secant_rigidity_pressure,
    derived_projective_pressure_secant_rigidity_secant, hc0]

lemma derived_projective_pressure_secant_rigidity_radius_formula
    {tau0 tau1 c thetaStar : ℝ} (hc : 0 ≤ c) (hTheta0 : 0 < thetaStar)
    (hTheta1 : thetaStar < 1)
    (heq :
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c thetaStar =
        derived_projective_pressure_secant_rigidity_secant tau0 tau1 thetaStar) :
    ∀ N m n : ℕ, 0 < m → m < N →
      derived_projective_pressure_secant_rigidity_radius tau0 tau1 c N n =
        Real.exp ((1 - (n : ℝ) / N) * tau0) * Real.exp (((n : ℝ) / N) * tau1) := by
  have hc0 :
      c = 0 :=
    derived_projective_pressure_secant_rigidity_correction_vanishes hc hTheta0 hTheta1 heq
  intro N m n hm hmn
  rw [derived_projective_pressure_secant_rigidity_radius, hc0]
  dsimp [derived_projective_pressure_secant_rigidity_pressure,
    derived_projective_pressure_secant_rigidity_secant]
  simp [Real.exp_add]

/-- Paper label: `thm:derived-projective-pressure-secant-rigidity`. For the concrete convex
pressure interpolation `secant + c θ (θ - 1)`, equality with the endpoint secant at one interior
point forces `c = 0`; the whole interval is then affine, and the integer-anchor radii satisfy the
geometric interpolation law. -/
theorem paper_derived_projective_pressure_secant_rigidity :
    derived_projective_pressure_secant_rigidity_statement := by
  intro tau0 tau1 c thetaStar hc hTheta0 hTheta1 heq
  refine ⟨
    derived_projective_pressure_secant_rigidity_all_points hc hTheta0 hTheta1 heq,
    derived_projective_pressure_secant_rigidity_radius_formula hc hTheta0 hTheta1 heq⟩

end Omega.DerivedConsequences
