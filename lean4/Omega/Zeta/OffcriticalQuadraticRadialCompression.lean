import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.UnitCirclePhaseLogConditionNumbers
import Omega.Zeta.AppOffcriticalRadiusCompression

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic

/-- Exact precision-potential factorization for the off-critical boundary depth. -/
lemma appOffcriticalBoundaryDepth_precision_factorization (γ δ : ℝ) (hδ : 0 < δ) :
    appOffcriticalBoundaryDepth γ δ =
      4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) *
        ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
  have hone : 0 < 1 + γ ^ 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp :
      Real.exp (-phasePrecisionPotential γ) = 1 / (Real.pi * (1 + γ ^ 2)) := by
    unfold phasePrecisionPotential
    calc
      Real.exp (-(Real.log Real.pi + Real.log (1 + γ ^ 2)))
          = Real.exp (-Real.log Real.pi) * Real.exp (-Real.log (1 + γ ^ 2)) := by
              rw [neg_add, Real.exp_add]
      _ = (Real.pi)⁻¹ * (1 + γ ^ 2)⁻¹ := by
            rw [Real.exp_neg, Real.exp_neg, Real.exp_log hpi, Real.exp_log hone]
      _ = 1 / (Real.pi * (1 + γ ^ 2)) := by
            field_simp
  rw [appOffcriticalBoundaryDepth_closed_form γ δ hδ, hexp]
  have hden_ne : γ ^ 2 + (1 + δ) ^ 2 ≠ 0 := by positivity
  field_simp [hden_ne]
  ring

/-- Publication-facing off-critical wrapper combining the exact Cayley closed forms, the boundary
depth channel identity, and the precision-potential factorization.
    thm:xi-offcritical-quadratic-radial-compression -/
theorem paper_xi_offcritical_quadratic_radial_compression (γ δ : ℝ) (hδ : 0 < δ) :
    (appOffcriticalModSq γ δ < 1 ∧
      appOffcriticalModSq γ δ =
        (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) ∧
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) ∧
      appOffcriticalBoundaryDepth γ δ = CayleyDepthIdentity.cayleyDepth δ γ 0 ∧
      appOffcriticalBoundaryDepth γ δ =
        4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) *
          ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨appOffcriticalModSq_lt_one γ δ hδ, appOffcriticalModSq_closed_form γ δ,
      appOffcriticalBoundaryDepth_closed_form γ δ hδ⟩
  · unfold appOffcriticalBoundaryDepth appOffcriticalModSq
    simpa using CayleyDepthIdentity.one_sub_cayleyModSq_eq_cayleyDepth δ γ 0 hδ
  · exact appOffcriticalBoundaryDepth_precision_factorization γ δ hδ

end Omega.Zeta
