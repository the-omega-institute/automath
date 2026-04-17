import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Multiscale

noncomputable section

/-- Concrete finite-level data for the normalized `L²` Stokes pullback scaling on a solenoid.
The pullback norm evolves by a fixed Jacobian factor `q / r`, starting from the base level `0`. -/
structure SolenoidNormalizedStokesL2ScalingData where
  q : ℕ
  r : ℕ
  pullbackNorm : ℕ → ℝ
  baseNorm : ℝ
  hr_pos : 0 < r
  baseNorm_nonneg : 0 ≤ baseNorm
  levelZero : pullbackNorm 0 = baseNorm
  scaling : ∀ n, pullbackNorm (n + 1) = ((q : ℝ) / r) * pullbackNorm n

namespace SolenoidNormalizedStokesL2ScalingData

/-- The normalized Jacobian factor appearing at each pullback step. -/
def scalingRatio (D : SolenoidNormalizedStokesL2ScalingData) : ℝ :=
  (D.q : ℝ) / D.r

/-- Iterating the pullback scaling law gives an exact closed form. -/
def closedForm (D : SolenoidNormalizedStokesL2ScalingData) : Prop :=
  ∀ n, D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n

/-- In the critical degree `q = r`, the normalization exactly preserves the base `L²` norm. -/
def criticalInvariant (D : SolenoidNormalizedStokesL2ScalingData) : Prop :=
  D.q = D.r → ∀ n, D.pullbackNorm n = D.baseNorm

/-- In the subcritical degree `q < r`, the normalized pullback ratio is strictly below `1`, so the
sequence stays bounded above by the base norm. -/
def subcriticalDecay (D : SolenoidNormalizedStokesL2ScalingData) : Prop :=
  D.q < D.r → D.scalingRatio < 1 ∧ ∀ n, D.pullbackNorm n ≤ D.baseNorm

lemma closedForm_of_scaling (D : SolenoidNormalizedStokesL2ScalingData) : D.closedForm := by
  intro n
  induction n with
  | zero =>
      simpa [closedForm, scalingRatio] using D.levelZero
  | succ n ih =>
      calc
        D.pullbackNorm (n + 1) = D.scalingRatio * D.pullbackNorm n := by
          simpa [scalingRatio] using D.scaling n
        _ = D.scalingRatio * (D.baseNorm * D.scalingRatio ^ n) := by rw [ih]
        _ = D.baseNorm * D.scalingRatio ^ (n + 1) := by
          rw [pow_succ]
          ring

lemma criticalInvariant_of_closedForm (D : SolenoidNormalizedStokesL2ScalingData) :
    D.closedForm → D.criticalInvariant := by
  intro hClosed hqr n
  have hRatio : D.scalingRatio = 1 := by
    unfold scalingRatio
    rw [hqr, div_self]
    exact_mod_cast D.hr_pos.ne'
  calc
    D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n := hClosed n
    _ = D.baseNorm := by simp [hRatio]

lemma subcriticalDecay_of_closedForm (D : SolenoidNormalizedStokesL2ScalingData) :
    D.closedForm → D.subcriticalDecay := by
  intro hClosed hqr
  have hr : (0 : ℝ) < D.r := by exact_mod_cast D.hr_pos
  have hRatioLt : D.scalingRatio < 1 := by
    unfold scalingRatio
    rw [div_lt_iff₀ hr]
    simpa using (show (D.q : ℝ) < D.r by exact_mod_cast hqr)
  have hRatioNonneg : 0 ≤ D.scalingRatio := by
    unfold scalingRatio
    positivity
  refine ⟨hRatioLt, ?_⟩
  intro n
  calc
    D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n := hClosed n
    _ ≤ D.baseNorm * 1 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_one₀ hRatioNonneg hRatioLt.le) D.baseNorm_nonneg
    _ = D.baseNorm := by ring

end SolenoidNormalizedStokesL2ScalingData

/-- Finite-level pullback scaling iterates to the closed form; in the critical degree the
normalization is invariant, while in the subcritical degree the normalized norm decays relative to
the base scale.
    thm:app-solenoid-normalized-stokes-l2-scaling-critical-degree -/
theorem paper_app_solenoid_normalized_stokes_l2_scaling_critical_degree
    (D : SolenoidNormalizedStokesL2ScalingData) :
    D.closedForm ∧ D.criticalInvariant ∧ D.subcriticalDecay := by
  have hClosed : D.closedForm := D.closedForm_of_scaling
  exact ⟨hClosed, D.criticalInvariant_of_closedForm hClosed, D.subcriticalDecay_of_closedForm hClosed⟩

end

end Omega.Multiscale
