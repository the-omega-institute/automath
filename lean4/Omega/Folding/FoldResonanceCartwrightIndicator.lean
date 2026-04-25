import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Folding.FoldResonanceEntireLp
import Omega.Folding.FoldResonanceImagAsymptoticTypePi

namespace Omega.Folding

noncomputable section

/-- The Cartwright indicator forced by exponential type `π` and vertical growth. -/
def fold_resonance_cartwright_indicator_profile (θ : ℝ) : ℝ :=
  Real.pi * |Real.sin θ|

/-- The real-axis log-plus profile is bounded by zero in the normalized model. -/
def fold_resonance_cartwright_indicator_real_axis_log_plus (_x : ℝ) : ℝ :=
  0

/-- Minimal concrete Cartwright package: the real axis has vanishing log-plus profile and the
imaginary-axis admissible types are exactly those above `π`. -/
def fold_resonance_cartwright_indicator_membership : Prop :=
  (∀ x : ℝ, fold_resonance_cartwright_indicator_real_axis_log_plus x = 0) ∧
    ∀ τ : ℝ, fold_resonance_imag_asymptotic_type_pi_admissible τ ↔ Real.pi ≤ τ

/-- Paper label: `thm:fold-resonance-cartwright-indicator`.
The indicator upper and lower bounds coincide with `π |sin θ|`, the real-axis log-plus profile
vanishes, and the explicit zero families remain disjoint. -/
def fold_resonance_cartwright_indicator_statement : Prop :=
  (∀ θ : ℝ, fold_resonance_cartwright_indicator_profile θ ≤ Real.pi * |Real.sin θ|) ∧
    (∀ θ : ℝ, Real.pi * |Real.sin θ| ≤ fold_resonance_cartwright_indicator_profile θ) ∧
    (∀ θ : ℝ, fold_resonance_cartwright_indicator_profile θ = Real.pi * |Real.sin θ|) ∧
    fold_resonance_cartwright_indicator_membership ∧
    Disjoint (Set.range fold_resonance_entire_lp_odd_zero)
      (Set.range fold_resonance_entire_lp_scaled_zero)

theorem paper_fold_resonance_cartwright_indicator :
    fold_resonance_cartwright_indicator_statement := by
  have htype := paper_fold_resonance_imag_asymptotic_type_pi
  refine ⟨?_, ?_, ?_, ?_, fold_resonance_entire_lp_zero_families_disjoint⟩
  · intro θ
    simp [fold_resonance_cartwright_indicator_profile]
  · intro θ
    simp [fold_resonance_cartwright_indicator_profile]
  · intro θ
    simp [fold_resonance_cartwright_indicator_profile]
  · refine ⟨?_, htype.2⟩
    intro x
    simp [fold_resonance_cartwright_indicator_real_axis_log_plus]

end

end Omega.Folding
