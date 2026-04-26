import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- A concrete power-law model for the minimal phase separation at scale `B`. -/
def xi_cdim_phase_compression_aliasing_exponent_delta (r d : ℕ) (B : ℝ) : ℝ :=
  B ^ (-((r : ℝ) / d))

private lemma xi_cdim_phase_compression_aliasing_exponent_delta_inv
    (r d : ℕ) {B : ℝ} (hB : 1 < B) :
    1 / xi_cdim_phase_compression_aliasing_exponent_delta r d B = B ^ ((r : ℝ) / d) := by
  unfold xi_cdim_phase_compression_aliasing_exponent_delta
  rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hB)), one_div]
  simp

/-- Paper label: `thm:xi-cdim-phase-compression-aliasing-exponent`. The Lean statement records the
exact `r / d` logarithmic exponent of the explicit power-law separation model. -/
theorem paper_xi_cdim_phase_compression_aliasing_exponent
    (r d : ℕ) (hd : 0 < d) {B : ℝ} (hB : 1 < B) :
    let α : ℝ := (r : ℝ) / d
    xi_cdim_phase_compression_aliasing_exponent_delta r d B = B ^ (-α) ∧
      1 / xi_cdim_phase_compression_aliasing_exponent_delta r d B = B ^ α ∧
      Real.log (1 / xi_cdim_phase_compression_aliasing_exponent_delta r d B) / Real.log B = α := by
  dsimp
  refine ⟨rfl, xi_cdim_phase_compression_aliasing_exponent_delta_inv r d hB, ?_⟩
  rw [xi_cdim_phase_compression_aliasing_exponent_delta_inv r d hB, Real.log_rpow]
  · field_simp [Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hB) hB.ne']
  · exact lt_trans zero_lt_one hB

end

end Omega.Zeta
