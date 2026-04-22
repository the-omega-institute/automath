import Omega.CircleDimension.ToeplitzGapSchurContraction

namespace Omega.CircleDimension

/-- Concrete radius-`r` Toeplitz/Carathéodory stability package near the critical line. -/
structure ToeplitzGapStabilityRHData where
  r : ℝ
  delta : ℝ
  q : ℝ
  C : Complex → Complex
  S : Complex → Complex
  hr : 0 < r ∧ r < 1
  hdelta : 0 < delta
  hbuffer : ∀ z : Complex, Complex.abs z ≤ r → delta ≤ Complex.re (C z)
  hgrowth : ∀ z : Complex, Complex.abs z ≤ r → Complex.abs (C z) ≤ (1 + r) / (1 - r)
  hS : ∀ z : Complex, S z = (C z - 1) / (C z + 1)
  hq : q = Real.sqrt (1 - delta * (1 - r) ^ 2)

/-- Paper label: `cor:cdim-toeplitz-gap-stability-rh`. -/
theorem paper_cdim_toeplitz_gap_stability_rh (D : ToeplitzGapStabilityRHData) :
    ∀ z : Complex,
      Complex.abs z ≤ D.r → D.delta ≤ Complex.re (D.C z) ∧ Complex.abs (D.S z) ≤ D.q := by
  intro z hz
  refine ⟨D.hbuffer z hz, ?_⟩
  have hschur :=
    paper_cdim_toeplitz_gap_schur_contraction D.delta D.r D.C D.S D.hr D.hdelta D.hbuffer
      D.hgrowth D.hS z hz
  simpa [D.hq] using hschur

end Omega.CircleDimension
