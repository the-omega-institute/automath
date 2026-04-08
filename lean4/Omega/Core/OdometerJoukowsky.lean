import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace Omega.POM

/-- Joukowsky map `J(z) = z + z⁻¹`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
noncomputable def joukowsky (z : ℂ) : ℂ := z + z⁻¹

/-- `J(1) = 2`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_one : joukowsky 1 = 2 := by
  unfold joukowsky; norm_num

/-- `J(-1) = -2`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_neg_one : joukowsky (-1) = -2 := by
  unfold joukowsky; norm_num

/-- `J(i) = 0`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_I : joukowsky Complex.I = 0 := by
  unfold joukowsky
  rw [Complex.inv_I]
  ring

/-- Main Euler identity: `J(e^{iθ}) = 2 cos θ`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_exp_I_mul (θ : ℝ) :
    joukowsky (Complex.exp ((θ : ℂ) * Complex.I)) = 2 * (Real.cos θ : ℂ) := by
  unfold joukowsky
  rw [← Complex.exp_neg]
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp
  ring

/-- On the unit circle, ‖J(e^{iθ})‖ ≤ 2.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_unit_circle_abs_le (θ : ℝ) :
    ‖joukowsky (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ 2 := by
  rw [joukowsky_exp_I_mul]
  rw [show (2 : ℂ) * (Real.cos θ : ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real]
  have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  show |2 * Real.cos θ| ≤ 2
  rw [abs_le]
  constructor <;> linarith

/-- Joukowsky is invariant under `z ↦ z⁻¹`.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem joukowsky_symmetric (z : ℂ) (_hz : z ≠ 0) :
    joukowsky z = joukowsky z⁻¹ := by
  unfold joukowsky
  rw [inv_inv]
  ring

/-- Paper package: Joukowsky / Pontryagin / Euler scaffolding.
    cor:pom-s4-odometer-pontryagin-joukowsky -/
theorem paper_pom_s4_odometer_pontryagin_joukowsky :
    joukowsky 1 = 2 ∧
    joukowsky (-1) = -2 ∧
    joukowsky Complex.I = 0 ∧
    (∀ θ : ℝ,
      joukowsky (Complex.exp ((θ : ℂ) * Complex.I)) = 2 * (Real.cos θ : ℂ)) ∧
    (∀ θ : ℝ,
      ‖joukowsky (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ 2) ∧
    (∀ z : ℂ, z ≠ 0 → joukowsky z = joukowsky z⁻¹) :=
  ⟨joukowsky_one, joukowsky_neg_one, joukowsky_I,
   joukowsky_exp_I_mul, joukowsky_unit_circle_abs_le, joukowsky_symmetric⟩

end Omega.POM
