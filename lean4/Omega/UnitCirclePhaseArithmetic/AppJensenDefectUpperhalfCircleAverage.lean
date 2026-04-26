import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- Explicit upper-half-plane parametrization of the radius-`ρ` Cayley preimage circle. -/
def app_jensen_defect_upperhalf_circle_average_point (ρ θ : ℝ) : ℂ :=
  let denom : ℝ := 1 + ρ ^ 2 + 2 * ρ * Real.cos θ
  ⟨(2 * ρ * Real.sin θ) / denom, (1 - ρ ^ 2) / denom⟩

/-- Finite sampled upper-half-plane circle average. -/
def app_jensen_defect_upperhalf_circle_average_sample
    (ρ : ℝ) (angles : Finset ℝ) (f : ℂ → ℝ) : ℝ :=
  Finset.sum angles (fun θ => f (app_jensen_defect_upperhalf_circle_average_point ρ θ)) /
    angles.card

lemma app_jensen_defect_upperhalf_circle_average_denom_pos
    {ρ θ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < 1 + ρ ^ 2 + 2 * ρ * Real.cos θ := by
  have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  nlinarith

lemma app_jensen_defect_upperhalf_circle_average_point_re
    {ρ θ : ℝ} (_hρ0 : 0 < ρ) (_hρ1 : ρ < 1) :
    (app_jensen_defect_upperhalf_circle_average_point ρ θ).re =
      (2 * ρ * Real.sin θ) / (1 + ρ ^ 2 + 2 * ρ * Real.cos θ) := by
  rfl

lemma app_jensen_defect_upperhalf_circle_average_point_im
    {ρ θ : ℝ} (_hρ0 : 0 < ρ) (_hρ1 : ρ < 1) :
    (app_jensen_defect_upperhalf_circle_average_point ρ θ).im =
      (1 - ρ ^ 2) / (1 + ρ ^ 2 + 2 * ρ * Real.cos θ) := by
  rfl

lemma app_jensen_defect_upperhalf_circle_average_im_pos
    {ρ θ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < (app_jensen_defect_upperhalf_circle_average_point ρ θ).im := by
  rw [app_jensen_defect_upperhalf_circle_average_point_im hρ0 hρ1]
  refine div_pos ?_ (app_jensen_defect_upperhalf_circle_average_denom_pos hρ0 hρ1)
  nlinarith

/-- Paper label: `prop:app-jensen-defect-upperhalf-circle-average`.
For `0 < ρ < 1`, the upper-half-plane circle model has explicit real and imaginary coordinates, and
any finite sampled circle average is exactly the average taken over this closed form. -/
theorem paper_app_jensen_defect_upperhalf_circle_average
    (ρ : ℝ) (angles : Finset ℝ) (f : ℂ → ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ θ ∈ angles,
      (app_jensen_defect_upperhalf_circle_average_point ρ θ).re =
          (2 * ρ * Real.sin θ) / (1 + ρ ^ 2 + 2 * ρ * Real.cos θ) ∧
        (app_jensen_defect_upperhalf_circle_average_point ρ θ).im =
          (1 - ρ ^ 2) / (1 + ρ ^ 2 + 2 * ρ * Real.cos θ)) ∧
      app_jensen_defect_upperhalf_circle_average_sample ρ angles f =
        Finset.sum angles (fun θ => f (app_jensen_defect_upperhalf_circle_average_point ρ θ)) /
          angles.card ∧
      ∀ θ ∈ angles, 0 < (app_jensen_defect_upperhalf_circle_average_point ρ θ).im := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ
    exact ⟨app_jensen_defect_upperhalf_circle_average_point_re hρ0 hρ1,
      app_jensen_defect_upperhalf_circle_average_point_im hρ0 hρ1⟩
  · rfl
  · intro θ hθ
    exact app_jensen_defect_upperhalf_circle_average_im_pos hρ0 hρ1

end

end Omega.UnitCirclePhaseArithmetic
