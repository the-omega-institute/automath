import Omega.Folding.StokesDefectHaarMixing

namespace Omega.Folding

/-- Error term controlling parity characters against Haar. -/
def parityCharacterGap (m n : ℕ) : ℝ :=
  2 * stokesDefectTVDist m n

/-- Full-support specialization of the parity-character error term. -/
def fullSupportParityGap (m n : ℕ) : ℝ :=
  2 * stokesDefectTVDist m n

/-- Error term for the Hamming-weight law against the binomial limit. -/
def hammingWeightBinomialGap (m n : ℕ) : ℝ :=
  stokesDefectTVDist m n

/-- Paper-facing corollary: exponential Haar mixing forces the parity characters to polarize at
    the same rate, and in the full-support case the Hamming-weight law inherits the same
    exponential control.
    cor:fold-stokes-defect-parity-polarization -/
theorem paper_fold_stokes_defect_parity_polarization (m : ℕ) :
    ∃ C η : ℝ, 0 < η ∧ η < 1 ∧
      (∀ n, m ≤ n → parityCharacterGap m n ≤ 2 * C * η ^ (n - m)) ∧
      (∀ n, m ≤ n → fullSupportParityGap m n ≤ 2 * C * η ^ (n - m)) ∧
      (∀ n, m ≤ n → hammingWeightBinomialGap m n ≤ C * η ^ (n - m)) := by
  obtain ⟨C, η, hη0, hη1, hmix⟩ := paper_fold_stokes_defect_haar_mixing m
  refine ⟨C, η, hη0, hη1, ?_, ?_, ?_⟩
  · intro n hn
    dsimp [parityCharacterGap]
    have h := hmix n hn
    nlinarith
  · intro n hn
    dsimp [fullSupportParityGap]
    have h := hmix n hn
    nlinarith
  · intro n hn
    simpa [hammingWeightBinomialGap] using hmix n hn

end Omega.Folding
