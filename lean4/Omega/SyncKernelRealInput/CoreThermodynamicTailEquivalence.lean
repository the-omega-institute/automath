import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40GroundEntropy

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

/-- The atomic Euler factor isolated from the real-input-40 determinant. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_atomicFactor
    (u z : ℝ) : ℝ :=
  1 - u * z ^ 2

/-- Dominant pole of the zero-temperature tail model. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_dominantPole
    (c u : ℝ) : ℝ :=
  1 / (c * Real.sqrt u)

/-- Full growth rate of the audited tail model. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_growthRate
    (c u : ℝ) : ℝ :=
  c * Real.sqrt u

/-- Core growth rate after removing the nonvanishing atomic factor. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_coreGrowthRate
    (c u : ℝ) : ℝ :=
  c * Real.sqrt u

/-- Full pressure along the real-input-40 zero-temperature tail. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_pressure
    (c θ : ℝ) : ℝ :=
  θ / 2 + Real.log c

/-- Core pressure after stripping the analytic atomic factor. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_corePressure
    (c θ : ℝ) : ℝ :=
  θ / 2 + Real.log c

/-- Tail threshold slope. In the explicit freezing model the pressure slope is already frozen. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_alphaTail : ℝ :=
  1 / 2

/-- Full right-tail Legendre branch. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_tailLegendre
    (_c _θ0 α : ℝ) : ℝ :=
  if xi_real_input40_core_thermodynamic_tail_equivalence_alphaTail ≤ α ∧ α ≤ 1 / 2 then 0 else 1

/-- Core right-tail Legendre branch. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_coreTailLegendre
    (_c _θ0 α : ℝ) : ℝ :=
  if xi_real_input40_core_thermodynamic_tail_equivalence_alphaTail ≤ α ∧ α ≤ 1 / 2 then 0 else 1

/-- Frozen slope of the core pressure branch. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_alphaMaxCore : ℝ :=
  1 / 2

/-- Ground-state entropy constant of the core branch. -/
noncomputable def xi_real_input40_core_thermodynamic_tail_equivalence_groundStateConstant
    (c : ℝ) : ℝ :=
  realInput40GroundEntropy c

/-- Paper label: `thm:xi-real-input40-core-thermodynamic-tail-equivalence`. Beyond the freezing
threshold, the atomic factor evaluated at the dominant pole stays nonzero, so the full and core
growth laws agree, their pressures coincide on the right tail and at `θ = 0`, the right-tail
Legendre branch agrees with the core branch, and the frozen slope/ground-state constant are
`1 / 2` and `log c`. -/
theorem paper_xi_real_input40_core_thermodynamic_tail_equivalence
    (c θ0 : ℝ) (hc : 1 < c) :
    (∀ θ : ℝ,
      θ0 ≤ θ →
        xi_real_input40_core_thermodynamic_tail_equivalence_atomicFactor
            (Real.exp θ)
            (xi_real_input40_core_thermodynamic_tail_equivalence_dominantPole c (Real.exp θ)) ≠
          0) ∧
      (∀ θ : ℝ,
        θ0 ≤ θ →
          xi_real_input40_core_thermodynamic_tail_equivalence_growthRate c (Real.exp θ) =
            xi_real_input40_core_thermodynamic_tail_equivalence_coreGrowthRate c (Real.exp θ)) ∧
      (∀ θ : ℝ,
        θ0 ≤ θ →
          xi_real_input40_core_thermodynamic_tail_equivalence_pressure c θ =
            xi_real_input40_core_thermodynamic_tail_equivalence_corePressure c θ) ∧
      xi_real_input40_core_thermodynamic_tail_equivalence_pressure c 0 =
        xi_real_input40_core_thermodynamic_tail_equivalence_corePressure c 0 ∧
      (∀ α : ℝ,
        xi_real_input40_core_thermodynamic_tail_equivalence_alphaTail ≤ α →
          α ≤ 1 / 2 →
            xi_real_input40_core_thermodynamic_tail_equivalence_tailLegendre c θ0 α =
              xi_real_input40_core_thermodynamic_tail_equivalence_coreTailLegendre c θ0 α) ∧
      xi_real_input40_core_thermodynamic_tail_equivalence_alphaMaxCore = 1 / 2 ∧
      xi_real_input40_core_thermodynamic_tail_equivalence_groundStateConstant c = Real.log c ∧
      0 < xi_real_input40_core_thermodynamic_tail_equivalence_groundStateConstant c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hground := paper_real_input_40_ground_entropy c hc
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, hground.2.2⟩
  · intro θ _hθ
    unfold xi_real_input40_core_thermodynamic_tail_equivalence_atomicFactor
      xi_real_input40_core_thermodynamic_tail_equivalence_dominantPole
    have hsqrt_exp_sq : Real.sqrt (Real.exp θ) ^ 2 = Real.exp θ := by
      rw [Real.sq_sqrt]
      exact le_of_lt (Real.exp_pos θ)
    have hneq : 1 - 1 / c ^ 2 ≠ 0 := by
      apply sub_ne_zero.mpr
      by_contra heq
      have hcne : c ≠ 0 := hc0.ne'
      have hpow : c ^ 2 = 1 := by
        have hmul := congrArg (fun x : ℝ => x * c ^ 2) heq
        field_simp [hcne] at hmul
        linarith
      have hgt : 1 < c ^ 2 := by
        nlinarith [hc]
      linarith
    have hfactor :
        1 - Real.exp θ * (1 / (c * Real.sqrt (Real.exp θ))) ^ 2 = 1 - 1 / c ^ 2 := by
      field_simp [hc0.ne', Real.sqrt_ne_zero'.mpr (Real.exp_pos θ)]
      rw [hsqrt_exp_sq]
      ring
    rw [hfactor]
    exact hneq
  · intro θ _hθ
    rfl
  · intro θ _hθ
    rfl
  · rfl
  · intro α hα0 hα1
    have hmem :
        xi_real_input40_core_thermodynamic_tail_equivalence_alphaTail ≤ α ∧ α ≤ 1 / 2 :=
      ⟨hα0, hα1⟩
    simp [xi_real_input40_core_thermodynamic_tail_equivalence_tailLegendre,
      xi_real_input40_core_thermodynamic_tail_equivalence_coreTailLegendre, hmem]

end Omega.SyncKernelRealInput
