import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The baseline phase is the regime where the energy exponent is exactly the untwisted one. -/
def gm_energy_exponent_twist_criterion_baseline_phase
    (baselineExponent energyExponent : ℝ) : Prop :=
  energyExponent = baselineExponent

/-- The phase-transition regime is the strict uplift above the baseline exponent. -/
def gm_energy_exponent_twist_criterion_phase_transition
    (baselineExponent energyExponent : ℝ) : Prop :=
  baselineExponent < energyExponent

/-- Nonresonant bookkeeping: the twisted radius sits a definite gap below the Perron radius, and
the resulting twisted error term is nonpositive in the energy decomposition. -/
def gm_energy_exponent_twist_criterion_nonresonant_case
    (baselineExponent energyExponent perronRadius twistedRadius uniformGap twistedError : ℝ) :
    Prop :=
  twistedRadius ≤ perronRadius - uniformGap ∧
    0 < uniformGap ∧
    twistedError ≤ 0 ∧
    energyExponent = max baselineExponent (baselineExponent + twistedError)

/-- Resonant bookkeeping: an equal-radius twist contributes a positive main-arc term to the
energy decomposition. -/
def gm_energy_exponent_twist_criterion_resonant_case
    (baselineExponent energyExponent perronRadius twistedRadius mainArcContribution : ℝ) : Prop :=
  twistedRadius = perronRadius ∧
    0 < mainArcContribution ∧
    energyExponent = max baselineExponent (baselineExponent + mainArcContribution)

/-- Paper label: `thm:gm-energy-exponent-twist-criterion`.
Uniform twisted-gap domination keeps the energy exponent in the baseline phase, while an
equal-radius twist with a positive main-arc contribution forces a phase transition. -/
theorem paper_gm_energy_exponent_twist_criterion
    (baselineExponent energyExponent perronRadius twistedRadius uniformGap twistedError
      mainArcContribution : ℝ) :
    (gm_energy_exponent_twist_criterion_nonresonant_case baselineExponent energyExponent
        perronRadius twistedRadius uniformGap twistedError →
      gm_energy_exponent_twist_criterion_baseline_phase baselineExponent energyExponent) ∧
    (gm_energy_exponent_twist_criterion_resonant_case baselineExponent energyExponent
        perronRadius twistedRadius mainArcContribution →
      gm_energy_exponent_twist_criterion_phase_transition baselineExponent energyExponent) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨_, _, herror, henergy⟩
    unfold gm_energy_exponent_twist_criterion_baseline_phase
    rw [henergy]
    apply max_eq_left
    linarith
  · intro h
    rcases h with ⟨_, hmain, henergy⟩
    unfold gm_energy_exponent_twist_criterion_phase_transition
    have huplift : baselineExponent < baselineExponent + mainArcContribution := by
      linarith
    rw [henergy, max_eq_right (le_of_lt huplift)]
    exact huplift

end Omega.SyncKernelWeighted
