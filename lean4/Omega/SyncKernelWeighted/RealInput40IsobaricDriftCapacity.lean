import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

abbrev RealInput40IsobaricAmbient :=
  EuclideanSpace ℝ (Fin 2)

def realInput40Inner (x y : RealInput40IsobaricAmbient) : ℝ :=
  @inner ℝ RealInput40IsobaricAmbient _ x y

/-- Concrete local bi-geometry data for the real-input-40 isobaric drift audit. The isobaric
slice is the hyperplane orthogonal to `gradP`, and `gradLogM` is decomposed into the component
parallel to `gradP` plus the orthogonal projection onto that slice. -/
structure RealInput40IsobaricDriftData where
  gradLogM : RealInput40IsobaricAmbient
  gradP : RealInput40IsobaricAmbient
  gradP_ne_zero : gradP ≠ 0

namespace RealInput40IsobaricDriftData

/-- Orthogonal projection of `gradLogM` onto the hyperplane orthogonal to `gradP`. -/
def isobaricProjection (D : RealInput40IsobaricDriftData) : RealInput40IsobaricAmbient :=
  D.gradLogM - (realInput40Inner D.gradLogM D.gradP / realInput40Inner D.gradP D.gradP) • D.gradP

/-- The projected isobaric drift is orthogonal to the pressure gradient. -/
def isobaricOrthogonality (D : RealInput40IsobaricDriftData) : Prop :=
  realInput40Inner D.isobaricProjection D.gradP = 0

/-- Tangent vectors to the isobaric slice. -/
def isobaricTangent (D : RealInput40IsobaricDriftData) (v : RealInput40IsobaricAmbient) : Prop :=
  realInput40Inner D.gradP v = 0

/-- On every isobaric tangent direction, the drift seen by `gradLogM` is controlled by the norm
of the projected drift; this is the Hilbert-space optimality statement used in the paper. -/
def isobaricOptimality (D : RealInput40IsobaricDriftData) : Prop :=
  ∀ v : RealInput40IsobaricAmbient, D.isobaricTangent v →
    |realInput40Inner D.gradLogM v| ≤ ‖D.isobaricProjection‖ * ‖v‖

end RealInput40IsobaricDriftData

open RealInput40IsobaricDriftData

/-- Paper label: `prop:real-input-40-isobaric-drift-capacity`. The explicit projection formula is
orthogonal to `gradP`, and on the isobaric slice the discarded parallel component contributes
nothing, so Cauchy--Schwarz bounds every directional drift by the norm of the projected
component. -/
theorem paper_real_input_40_isobaric_drift_capacity (D : RealInput40IsobaricDriftData) :
    D.isobaricOrthogonality ∧ D.isobaricOptimality := by
  have hpp_ne : realInput40Inner D.gradP D.gradP ≠ 0 := by
    unfold realInput40Inner
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr D.gradP_ne_zero)
  have hpp_ne_inner : inner ℝ D.gradP D.gradP ≠ 0 := by
    simpa [realInput40Inner] using hpp_ne
  have horth : D.isobaricOrthogonality := by
    unfold RealInput40IsobaricDriftData.isobaricOrthogonality
      RealInput40IsobaricDriftData.isobaricProjection
      realInput40Inner
    rw [inner_sub_left, real_inner_smul_left]
    have hcancel :
        inner ℝ D.gradLogM D.gradP / inner ℝ D.gradP D.gradP * inner ℝ D.gradP D.gradP =
          inner ℝ D.gradLogM D.gradP := by
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hpp_ne_inner, mul_one]
    linarith
  refine ⟨horth, ?_⟩
  intro v hv
  have hslice :
      realInput40Inner D.gradLogM v = realInput40Inner D.isobaricProjection v := by
    unfold RealInput40IsobaricDriftData.isobaricTangent at hv
    unfold RealInput40IsobaricDriftData.isobaricProjection
    unfold realInput40Inner at hv ⊢
    rw [inner_sub_left, real_inner_smul_left, hv, mul_zero, sub_zero]
  calc
    |realInput40Inner D.gradLogM v| = |realInput40Inner D.isobaricProjection v| := by rw [hslice]
    _ ≤ ‖D.isobaricProjection‖ * ‖v‖ := by
      simpa [realInput40Inner] using abs_real_inner_le_norm D.isobaricProjection v

end

end Omega.SyncKernelWeighted
