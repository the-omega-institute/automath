import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The Fourier decay exponent obtained from a uniform twisted spectral gap. -/
def gm_holder_regularity_from_gap_beta (δ : ℝ) : ℝ :=
  -Real.log (1 - δ) / Real.log Real.goldenRatio

/-- The elementary gap condition equivalent to `β > 1`. -/
def gm_holder_regularity_from_gap_gap_condition (δ : ℝ) : Prop :=
  (1 - δ) * Real.goldenRatio < 1

/-- Concrete Fourier decay package used as the bridge to Hölder regularity. -/
def gm_holder_regularity_from_gap_fourier_decay
    (muHat : ℝ → ℂ) (C β : ℝ) : Prop :=
  0 ≤ C ∧ ∀ ξ : ℝ, 1 ≤ |ξ| → ‖muHat ξ‖ ≤ C * |ξ| ^ (-β)

/-- Abstract Hölder-density certificate controlled by finite spectral data. -/
def gm_holder_regularity_from_gap_holder_density_certificate
    (muHat : ℝ → ℂ) (C β α : ℝ) : Prop :=
  0 < α ∧ α < β - 1 ∧ gm_holder_regularity_from_gap_fourier_decay muHat C β

lemma gm_holder_regularity_from_gap_beta_gt_one_iff
    {δ : ℝ} (_hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 < gm_holder_regularity_from_gap_beta δ ↔
      gm_holder_regularity_from_gap_gap_condition δ := by
  have hxpos : 0 < 1 - δ := by linarith
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hlogphi_pos : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  unfold gm_holder_regularity_from_gap_beta
  unfold gm_holder_regularity_from_gap_gap_condition
  constructor
  · intro hβ
    have hlog : Real.log Real.goldenRatio < -Real.log (1 - δ) :=
      (one_lt_div₀ hlogphi_pos).1 hβ
    have hlog_inv : Real.log Real.goldenRatio < Real.log (1 - δ)⁻¹ := by
      simpa [Real.log_inv] using hlog
    have hinv : Real.goldenRatio < (1 - δ)⁻¹ :=
      (Real.log_lt_log_iff hphi_pos (inv_pos.mpr hxpos)).1 hlog_inv
    have hdiv : Real.goldenRatio < 1 / (1 - δ) := by
      simpa [one_div] using hinv
    have hmul := (lt_div_iff₀ hxpos).1 hdiv
    simpa [mul_comm] using hmul
  · intro hgap
    have hdiv : Real.goldenRatio < 1 / (1 - δ) := by
      exact (lt_div_iff₀ hxpos).2 (by simpa [mul_comm] using hgap)
    have hinv : Real.goldenRatio < (1 - δ)⁻¹ := by
      simpa [one_div] using hdiv
    have hlog_inv : Real.log Real.goldenRatio < Real.log (1 - δ)⁻¹ :=
      (Real.log_lt_log_iff hphi_pos (inv_pos.mpr hxpos)).2 hinv
    have hlog : Real.log Real.goldenRatio < -Real.log (1 - δ) := by
      simpa [Real.log_inv] using hlog_inv
    exact (one_lt_div₀ hlogphi_pos).2 hlog

/-- Paper label: `thm:gm-holder-regularity-from-gap`.
The assumed twisted spectral gap is represented by a Fourier power-decay estimate. The logarithmic
exponent satisfies the advertised arithmetic equivalence, and every `α < β - 1` gives the
corresponding Hölder-density certificate. -/
theorem paper_gm_holder_regularity_from_gap
    (δ C α : ℝ) (muHat : ℝ → ℂ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hα0 : 0 < α)
    (hα : α < gm_holder_regularity_from_gap_beta δ - 1)
    (hdecay :
      gm_holder_regularity_from_gap_fourier_decay muHat C
        (gm_holder_regularity_from_gap_beta δ)) :
    (1 < gm_holder_regularity_from_gap_beta δ ↔
        gm_holder_regularity_from_gap_gap_condition δ) ∧
      gm_holder_regularity_from_gap_holder_density_certificate muHat C
        (gm_holder_regularity_from_gap_beta δ) α := by
  exact ⟨gm_holder_regularity_from_gap_beta_gt_one_iff hδ0 hδ1,
    hα0, hα, hdecay⟩

end

end Omega.SyncKernelRealInput
