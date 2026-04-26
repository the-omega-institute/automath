import Mathlib.Tactic
import Omega.Folding.FoldCriticalResonanceConstantExpRate
import Omega.Folding.FoldPairedStepDirichletCharacterIdentity
import Omega.Folding.ResidualPushforwardKernelByFiberProbability

namespace Omega.Folding

/-- Concrete package for the residual-pushforward spectral-gap upper bound. The recorded gap is
identified with the chapter-local Rayleigh-gap placeholder, while the two error terms are the
absolute deviations of the Fibonacci resonance channels from the limiting constant. -/
structure ResidualPushforwardGapUpperBoundData where
  kernel : PairedStepKernelData
  resonance : FoldCriticalResonanceConstantExpRateData
  resolution : ℝ
  gap : ℝ
  kappaPhi : ℝ
  expError : ℝ
  hresolution : 0 < resolution
  hgap : gap = kernel.spectralGap
  hkappaPhi :
    kappaPhi = |foldCriticalResonanceAmplitudeFm resonance.m - resonance.Cphi|
  hexpError :
    expError = |foldCriticalResonanceAmplitudeFmSucc resonance.m - resonance.Cphi|

/-- Paper label: `cor:fold-residual-pushforward-gap-upper-bound`.
The residual-pushforward gap is the Rayleigh-gap placeholder from the paired-step kernel package,
so it vanishes; the two resonance terms are absolute errors and hence nonnegative, which yields the
stated upper bound after division by the positive resolution parameter. -/
theorem paper_fold_residual_pushforward_gap_upper_bound
    (D : ResidualPushforwardGapUpperBoundData) :
    D.gap ≤ D.kappaPhi / D.resolution + D.expError / D.resolution := by
  have hgap0 : D.gap = 0 := by
    simpa [PairedStepKernelData.spectralGap] using D.hgap
  have hkappa_nonneg : 0 ≤ D.kappaPhi := by
    rw [D.hkappaPhi]
    positivity
  have hexp_nonneg : 0 ≤ D.expError := by
    rw [D.hexpError]
    positivity
  have hrhs_nonneg :
      0 ≤ D.kappaPhi / D.resolution + D.expError / D.resolution := by
    exact add_nonneg
      (div_nonneg hkappa_nonneg D.hresolution.le)
      (div_nonneg hexp_nonneg D.hresolution.le)
  rw [hgap0]
  exact hrhs_nonneg

end Omega.Folding
