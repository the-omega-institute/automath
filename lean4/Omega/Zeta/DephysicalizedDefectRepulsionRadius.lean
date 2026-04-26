import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion
import Omega.UnitCirclePhaseArithmetic.AppJensenRepulsionRadiusToOne
import Omega.UnitCirclePhaseArithmetic.AppJensenZeroRepulsionSubdisk

open Filter

namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion
open Omega.TypedAddressBiaxialCompletion.JensenCountableCriterionData
open Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Dephysicalized repulsion-radius notation attached to a radius/defect pair. -/
def dephys_defect_repulsion_radius (ρ Dζ : ℝ) : ℝ :=
  repulsionRadius ρ Dζ

/-- Paper label: `thm:dephys-defect-repulsion-radius`. The appendix repulsion-subdisk estimate,
the repulsion-radius notation, and the radius-to-one RH criterion are packaged into the
dephysicalized Zeta-facing wrapper. -/
theorem paper_dephys_defect_repulsion_radius
    (D : JensenCountableCriterionData) (roots : Finset ℂ)
    (hdefect :
      ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → D.defect ρ = appSingleZeroJensenDefect ρ roots)
    (hdiskZero : ¬ D.rh → ∃ a : ℂ, a ∈ roots ∧ 0 < ‖a‖ ∧ ‖a‖ < 1)
    (hrstar :
      ∃ ρseq : ℕ → ℝ,
        Monotone ρseq ∧
          Tendsto ρseq atTop (nhds 1) ∧
            (∀ n : ℕ, 0 < ρseq n ∧ ρseq n < 1) ∧
              Tendsto
                (fun n : ℕ =>
                  dephys_defect_repulsion_radius (ρseq n) (D.defect (ρseq n)))
                atTop
                (nhds 1)) :
    (∀ ρ Dζ, dephys_defect_repulsion_radius ρ Dζ = repulsionRadius ρ Dζ) ∧
      (∀ {a : ℂ}, a ∈ roots → 0 < ‖a‖ → ‖a‖ < 1 →
        ∀ {ρ : ℝ}, ‖a‖ < ρ → ρ < 1 →
          dephys_defect_repulsion_radius ρ (D.defect ρ) ≤ ‖a‖) ∧
      (∀ (ρ ε : ℝ), 0 < ρ → ρ < 1 → D.defect ρ ≤ ε →
        ρ * Real.exp (-ε) ≤ dephys_defect_repulsion_radius ρ (D.defect ρ)) ∧
      D.rh := by
  have hsubdisk := paper_app_jensen_zero_repulsion_subdisk
  refine ⟨fun ρ Dζ => rfl, ?_, ?_, ?_⟩
  · intro a ha_mem ha_pos ha_unit ρ hlt hρ
    have hρ_pos : 0 < ρ := lt_trans ha_pos hlt
    have hrepulsion :
        app_jensen_zero_repulsion_subdisk_rStar ρ (appSingleZeroJensenDefect ρ roots) ≤ ‖a‖ :=
      (hsubdisk.2 roots ha_mem ha_pos ha_unit hlt hρ).1
    simpa [dephys_defect_repulsion_radius, hdefect hρ_pos hρ] using hrepulsion
  · intro ρ ε hρ0 hρ1 hdefect_le
    let _ := hρ1
    unfold dephys_defect_repulsion_radius repulsionRadius
    have hexp_le : Real.exp (-ε) ≤ Real.exp (-(D.defect ρ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ0
    exact mul_le_mul_of_nonneg_left hexp_le hρ_nonneg
  · rcases hrstar with ⟨ρseq, hmono, hρtend, hρmem, hrstar_tend⟩
    exact
      paper_app_jensen_repulsion_radius_to_one D roots hdefect hdiskZero
        ⟨ρseq, hmono, hρtend, hρmem, by
          simpa [dephys_defect_repulsion_radius] using hrstar_tend⟩

end

end Omega.Zeta
