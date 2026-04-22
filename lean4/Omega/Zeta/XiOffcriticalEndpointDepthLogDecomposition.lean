import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.OffcriticalQuadraticRadialCompression

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:xi-offcritical-endpoint-depth-log-decomposition`. -/
theorem paper_xi_offcritical_endpoint_depth_log_decomposition
    (γ δ : ℝ) (hδ : 0 < δ) :
    let h := appOffcriticalBoundaryDepth γ δ
    h = 4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) *
          ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) ∧
      h / δ * Real.exp (phasePrecisionPotential γ) =
        4 * Real.pi * ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) ∧
      -Real.log h =
        phasePrecisionPotential γ + Real.log (1 / δ) - Real.log (4 * Real.pi) -
          Real.log ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
  let h := appOffcriticalBoundaryDepth γ δ
  have hfactor : h =
      4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) *
        ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
    simpa [h] using appOffcriticalBoundaryDepth_precision_factorization γ δ hδ
  have hratio_pos : 0 < ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
    positivity
  have hdepth_pos : 0 < h := by
    rw [hfactor]
    positivity
  have hprod :
      h / δ * Real.exp (phasePrecisionPotential γ) =
        4 * Real.pi * ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
    rw [hfactor]
    have hexp_cancel :
        Real.exp (-phasePrecisionPotential γ) * Real.exp (phasePrecisionPotential γ) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) *
            ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2))) / δ *
          Real.exp (phasePrecisionPotential γ) =
          4 * Real.pi * ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) *
            (Real.exp (-phasePrecisionPotential γ) *
              Real.exp (phasePrecisionPotential γ)) := by
            field_simp [hδ.ne']
      _ = 4 * Real.pi * ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
            simp [hexp_cancel]
  have hlog :
      -Real.log h =
        phasePrecisionPotential γ + Real.log (1 / δ) - Real.log (4 * Real.pi) -
          Real.log ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) := by
    have h4pi_ne : 4 * Real.pi ≠ 0 := by positivity
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hexp_ne : Real.exp (-phasePrecisionPotential γ) ≠ 0 := by positivity
    have hratio_ne : ((1 + γ ^ 2) / (γ ^ 2 + (1 + δ) ^ 2)) ≠ 0 := ne_of_gt hratio_pos
    rw [hfactor]
    rw [Real.log_mul (show 4 * Real.pi * δ * Real.exp (-phasePrecisionPotential γ) ≠ 0 by positivity)
      hratio_ne]
    rw [Real.log_mul (show 4 * Real.pi * δ ≠ 0 by positivity) hexp_ne]
    rw [Real.log_mul h4pi_ne hδne]
    rw [Real.log_exp]
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hδlog' : Real.log δ⁻¹ = -Real.log δ := by
      simpa [one_div] using hδlog
    ring_nf
    rw [hδlog']
    ring
  exact ⟨hfactor, hprod, hlog⟩

end Omega.Zeta
