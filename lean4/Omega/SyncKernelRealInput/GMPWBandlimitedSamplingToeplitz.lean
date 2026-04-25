import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete audit package for the Paley-Wiener sampling/Toeplitz finite-section comparison. -/
structure gm_pw_bandlimited_sampling_toeplitz_data where
  PaleyWiener : Type
  SequenceSpace : Type
  sample : PaleyWiener → SequenceSpace
  reconstruct : SequenceSpace → PaleyWiener
  continuousOperator : PaleyWiener → PaleyWiener
  sampledToeplitzOperator : SequenceSpace → SequenceSpace
  continuousOperatorNorm : ℝ
  sampledToeplitzOperatorNorm : ℝ
  finiteSectionTopEigenvalue : ℕ → ℝ
  finiteSectionTailBound : ℕ → ℝ
  sampling_left_inverse : ∀ f : PaleyWiener, reconstruct (sample f) = f
  conjugation_identity :
    ∀ f : PaleyWiener, sample (continuousOperator f) = sampledToeplitzOperator (sample f)
  norm_preservation : continuousOperatorNorm = sampledToeplitzOperatorNorm
  finite_section_tail :
    ∀ N : ℕ, |continuousOperatorNorm - finiteSectionTopEigenvalue N| ≤ finiteSectionTailBound N
  finite_section_tail_nonnegative : ∀ N : ℕ, 0 ≤ finiteSectionTailBound N

/-- The sampled Toeplitz model is the operator obtained after applying the sampling map. -/
def gm_pw_bandlimited_sampling_toeplitz_sampled_operator
    (D : gm_pw_bandlimited_sampling_toeplitz_data) :
    D.SequenceSpace → D.SequenceSpace :=
  D.sampledToeplitzOperator

/-- The finite truncation datum recorded at level `N`. -/
def gm_pw_bandlimited_sampling_toeplitz_finite_truncation
    (D : gm_pw_bandlimited_sampling_toeplitz_data) (N : ℕ) : ℝ :=
  D.finiteSectionTopEigenvalue N

/-- Paper-facing statement: the sampling/reconstruction pair intertwines the continuous operator
with the Toeplitz model, preserves the operator norm, and gives audited finite-section tails. -/
def gm_pw_bandlimited_sampling_toeplitz_statement
    (D : gm_pw_bandlimited_sampling_toeplitz_data) : Prop :=
  (∀ f : D.PaleyWiener, D.reconstruct (D.sample f) = f) ∧
    (∀ f : D.PaleyWiener,
      D.sample (D.continuousOperator f) =
        gm_pw_bandlimited_sampling_toeplitz_sampled_operator D (D.sample f)) ∧
    D.continuousOperatorNorm = D.sampledToeplitzOperatorNorm ∧
    (∀ N : ℕ,
      |D.continuousOperatorNorm -
          gm_pw_bandlimited_sampling_toeplitz_finite_truncation D N| ≤
        D.finiteSectionTailBound N) ∧
    ∀ N : ℕ, 0 ≤ D.finiteSectionTailBound N

/-- Paper label: `thm:gm-pw-bandlimited-sampling-toeplitz`. -/
theorem paper_gm_pw_bandlimited_sampling_toeplitz
    (D : gm_pw_bandlimited_sampling_toeplitz_data) :
    gm_pw_bandlimited_sampling_toeplitz_statement D := by
  refine ⟨D.sampling_left_inverse, ?_, D.norm_preservation, ?_, D.finite_section_tail_nonnegative⟩
  · intro f
    simpa [gm_pw_bandlimited_sampling_toeplitz_sampled_operator] using D.conjugation_identity f
  · intro N
    simpa [gm_pw_bandlimited_sampling_toeplitz_finite_truncation] using D.finite_section_tail N

end Omega.SyncKernelRealInput
