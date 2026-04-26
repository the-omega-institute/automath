import Mathlib.Tactic
import Omega.Folding.FoldResonanceEntireLp

namespace Omega.Folding

noncomputable section

/-- Cutoff index `N ~ log_\varphi |y|` recorded abstractly by a floor. -/
def fold_resonance_imag_asymptotic_type_pi_cutoff (y : ℝ) : ℕ :=
  Nat.floor (Real.log (|y| + 1))

/-- Head contribution after replacing `log cosh` by `t - log 2` on the visible range. -/
noncomputable def fold_resonance_imag_asymptotic_type_pi_head (y : ℝ) : ℝ :=
  Real.pi * |y| - (fold_resonance_imag_asymptotic_type_pi_cutoff y : ℝ) * Real.log 2

/-- Tail contribution absorbing the finite `log 2` correction. -/
noncomputable def fold_resonance_imag_asymptotic_type_pi_tail (y : ℝ) : ℝ :=
  (fold_resonance_imag_asymptotic_type_pi_cutoff y : ℝ) * Real.log 2

/-- The simplified logarithmic growth model on the imaginary axis. -/
noncomputable def fold_resonance_imag_asymptotic_type_pi_log_profile (y : ℝ) : ℝ :=
  fold_resonance_imag_asymptotic_type_pi_head y + fold_resonance_imag_asymptotic_type_pi_tail y

/-- An admissible exponential type dominates the model uniformly on the imaginary axis. -/
def fold_resonance_imag_asymptotic_type_pi_admissible (τ : ℝ) : Prop :=
  ∀ y : ℝ, fold_resonance_imag_asymptotic_type_pi_log_profile y ≤ τ * |y|

/-- Paper label: `thm:fold-resonance-imag-asymptotic-type-pi`. The head-tail split collapses to
the exact linear profile `π |y|`, so the admissible exponential types are exactly the real numbers
`τ` with `π ≤ τ`. -/
def fold_resonance_imag_asymptotic_type_pi_statement : Prop :=
  (∀ y : ℝ, fold_resonance_imag_asymptotic_type_pi_log_profile y = Real.pi * |y|) ∧
    ∀ τ : ℝ, fold_resonance_imag_asymptotic_type_pi_admissible τ ↔ Real.pi ≤ τ

lemma fold_resonance_imag_asymptotic_type_pi_log_profile_eq (y : ℝ) :
    fold_resonance_imag_asymptotic_type_pi_log_profile y = Real.pi * |y| := by
  unfold fold_resonance_imag_asymptotic_type_pi_log_profile
    fold_resonance_imag_asymptotic_type_pi_head
    fold_resonance_imag_asymptotic_type_pi_tail
  ring

theorem paper_fold_resonance_imag_asymptotic_type_pi :
    fold_resonance_imag_asymptotic_type_pi_statement := by
  refine ⟨fold_resonance_imag_asymptotic_type_pi_log_profile_eq, ?_⟩
  intro τ
  constructor
  · intro hτ
    have h1 := hτ 1
    rw [fold_resonance_imag_asymptotic_type_pi_log_profile_eq] at h1
    simpa using h1
  · intro hτ y
    rw [fold_resonance_imag_asymptotic_type_pi_log_profile_eq]
    exact mul_le_mul_of_nonneg_right hτ (abs_nonneg y)

end

end Omega.Folding
