import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion

noncomputable section

/-- The explicit repulsion radius attached to the Jensen defect at radius `ρ`. -/
def app_jensen_zero_repulsion_subdisk_rStar (ρ Dρ : ℝ) : ℝ :=
  ρ * Real.exp (-Dρ)

/-- Package for the Jensen-defect repulsion disk. The positive-norm hypothesis excludes the
spurious zero-root encoding issue. -/
def app_jensen_zero_repulsion_subdisk_package : Prop :=
  (∀ ρ Dρ : ℝ,
      app_jensen_zero_repulsion_subdisk_rStar ρ Dρ = repulsionRadius ρ Dρ) ∧
    ∀ (roots : Finset ℂ) {a : ℂ}, a ∈ roots → 0 < ‖a‖ → ‖a‖ < 1 →
      ∀ {ρ : ℝ}, ‖a‖ < ρ → ρ < 1 →
        let Dρ := appSingleZeroJensenDefect ρ roots
        app_jensen_zero_repulsion_subdisk_rStar ρ Dρ ≤ ‖a‖ ∧
          ¬ ‖a‖ < app_jensen_zero_repulsion_subdisk_rStar ρ Dρ

/-- Paper label: `prop:app-jensen-zero-repulsion-subdisk`. A positive-norm zero contributes a
nonnegative Jensen summand, so the Jensen defect at radius `ρ` forces the zero to lie outside the
repulsion subdisk of radius `r_*(ρ) = ρ exp (-D(ρ))`. -/
theorem paper_app_jensen_zero_repulsion_subdisk : app_jensen_zero_repulsion_subdisk_package := by
  refine ⟨?_, ?_⟩
  · intro ρ Dρ
    rfl
  · intro roots a ha_mem ha_pos ha_lt ρ hρ hρ_lt
    let Dρ := appSingleZeroJensenDefect ρ roots
    have hρpos : 0 < ρ := lt_trans ha_pos hρ
    have hLower :
        Real.log (ρ / ‖a‖) ≤ Dρ := by
      simpa [Dρ] using
        (paper_app_jensen_single_zero_lower_bound roots ha_mem ha_pos ha_lt).1 ρ hρ hρ_lt
    have hExp :
        ρ / ‖a‖ ≤ Real.exp Dρ := by
      have hdiv_pos : 0 < ρ / ‖a‖ := div_pos hρpos ha_pos
      calc
        ρ / ‖a‖ = Real.exp (Real.log (ρ / ‖a‖)) := by
          rw [Real.exp_log hdiv_pos]
        _ ≤ Real.exp Dρ := Real.exp_le_exp.mpr hLower
    have hRhoLe : ρ ≤ ‖a‖ * Real.exp Dρ := by
      have := (div_le_iff₀ ha_pos).mp hExp
      simpa [mul_comm] using this
    have hDiv :
        ρ / Real.exp Dρ ≤ ‖a‖ := by
      refine (div_le_iff₀ (Real.exp_pos Dρ)).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRhoLe
    have hRepulsion :
        app_jensen_zero_repulsion_subdisk_rStar ρ Dρ ≤ ‖a‖ := by
      simpa [app_jensen_zero_repulsion_subdisk_rStar, Real.exp_neg, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hDiv
    exact ⟨hRepulsion, not_lt.mpr hRepulsion⟩

end

end Omega.UnitCirclePhaseArithmetic
