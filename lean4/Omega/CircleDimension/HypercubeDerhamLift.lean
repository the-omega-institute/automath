import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Path-integral coefficient: false ↦ +1, true ↦ -1.
    prop:cdim-hypercube-derham-stokes-lift -/
def pathIntegralCoeff (ω_i : Bool) : ℤ := if ω_i then -1 else 1

/-- Coefficient at `false` equals `+1`.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegralCoeff_false : pathIntegralCoeff false = 1 := rfl

/-- Coefficient at `true` equals `-1`.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegralCoeff_true : pathIntegralCoeff true = -1 := rfl

/-- Coefficient has absolute value one.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegralCoeff_abs (b : Bool) : |pathIntegralCoeff b| = 1 := by
  cases b <;> rfl

/-- Coefficient squares to one.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegralCoeff_sq (b : Bool) :
    pathIntegralCoeff b * pathIntegralCoeff b = 1 := by
  cases b <;> rfl

/-- Abstract path integral: `π · coeff(ω_i)`.
    prop:cdim-hypercube-derham-stokes-lift -/
noncomputable def pathIntegral (ω_i : Bool) : ℝ :=
  Real.pi * (pathIntegralCoeff ω_i : ℝ)

/-- Path integral at `false` equals `π`.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegral_false : pathIntegral false = Real.pi := by
  unfold pathIntegral
  rw [pathIntegralCoeff_false]
  push_cast
  ring

/-- Path integral at `true` equals `-π`.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegral_true : pathIntegral true = -Real.pi := by
  unfold pathIntegral
  rw [pathIntegralCoeff_true]
  push_cast
  ring

/-- Dividing the path integral by π recovers the integer coefficient.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem pathIntegral_div_pi (b : Bool) (hpi : Real.pi ≠ 0) :
    pathIntegral b / Real.pi = (pathIntegralCoeff b : ℝ) := by
  unfold pathIntegral
  field_simp

/-- Paper package: hypercube de Rham / Stokes lift.
    prop:cdim-hypercube-derham-stokes-lift -/
theorem paper_cdim_hypercube_derham_stokes_lift :
    pathIntegralCoeff false = 1 ∧
    pathIntegralCoeff true = -1 ∧
    (∀ b : Bool, |pathIntegralCoeff b| = 1) ∧
    (∀ b : Bool, pathIntegralCoeff b * pathIntegralCoeff b = 1) ∧
    pathIntegral false = Real.pi ∧
    pathIntegral true = -Real.pi ∧
    (∀ b : Bool, Real.pi ≠ 0 →
      pathIntegral b / Real.pi = (pathIntegralCoeff b : ℝ)) :=
  ⟨pathIntegralCoeff_false,
   pathIntegralCoeff_true,
   pathIntegralCoeff_abs,
   pathIntegralCoeff_sq,
   pathIntegral_false,
   pathIntegral_true,
   pathIntegral_div_pi⟩

end Omega.CircleDimension
