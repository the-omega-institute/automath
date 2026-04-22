import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete package for the finite-frequency/finite-scale verification principle behind the
uniform twisted gap. The finite check set is encoded by `frequencySet × scaleSet`; the
nonresonant frequency window is represented by `window`, and the scale bootstrap starts at
`baseScale`. -/
structure GmFiniteVerificationUniformGapData where
  frequencySet : Finset ℝ
  scaleSet : Finset ℕ
  window : Set ℝ
  baseScale : ℕ
  gap : ℝ → ℕ → ℝ
  targetGap : ℝ
  sampled_frequency_mem_window :
    ∀ {θ : ℝ}, θ ∈ frequencySet → θ ∈ window
  sampled_scale_large :
    ∀ {M : ℕ}, M ∈ scaleSet → baseScale ≤ M
  frequency_window_cover :
    ∀ {θ : ℝ}, θ ∈ window →
      ∃ θ0 ∈ frequencySet, ∀ {M : ℕ}, baseScale ≤ M → gap θ M ≤ gap θ0 M
  scale_bootstrap :
    ∀ {θ : ℝ}, θ ∈ frequencySet →
      (∀ {M : ℕ}, M ∈ scaleSet → gap θ M ≤ targetGap) →
        ∀ {N : ℕ}, baseScale ≤ N → gap θ N ≤ targetGap

namespace GmFiniteVerificationUniformGapData

/-- Uniform twisted gap on the full nonresonant window above the bootstrap scale. -/
def uniform_gap_holds (D : GmFiniteVerificationUniformGapData) : Prop :=
  ∀ {θ : ℝ}, θ ∈ D.window → ∀ {N : ℕ}, D.baseScale ≤ N → D.gap θ N ≤ D.targetGap

/-- Finite verification on the sampled frequencies and sampled scales. -/
def finite_checks_pass (D : GmFiniteVerificationUniformGapData) : Prop :=
  ∀ {θ : ℝ}, θ ∈ D.frequencySet → ∀ {M : ℕ}, M ∈ D.scaleSet → D.gap θ M ≤ D.targetGap

end GmFiniteVerificationUniformGapData

open GmFiniteVerificationUniformGapData

/-- Paper label: `thm:gm-finite-verification-uniform-gap`. Restricting the uniform gap to the
finite sample set gives the forward implication, and the reverse implication combines the finite
frequency cover of the nonresonant window with the scale-bootstrap principle. -/
theorem paper_gm_finite_verification_uniform_gap (D : GmFiniteVerificationUniformGapData) :
    D.uniform_gap_holds ↔ D.finite_checks_pass := by
  constructor
  · intro hUniform θ hθ M hM
    exact hUniform (D.sampled_frequency_mem_window hθ) (D.sampled_scale_large hM)
  · intro hFinite θ hθ N hN
    rcases D.frequency_window_cover hθ with ⟨θ0, hθ0, hcompare⟩
    exact le_trans (hcompare hN) <| D.scale_bootstrap hθ0 (fun hM => hFinite hθ0 hM) hN

end Omega.SyncKernelWeighted
