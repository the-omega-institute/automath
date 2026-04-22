import Omega.Folding.FoldSpectrumParityZero

namespace Omega.Folding

/-- Paper label: `prop:fold-multiplicity-spectrum-blindspot-half`.
At the half-modulus character, the existing parity-zero factorization already forces the
fold-multiplicity Fourier transform to vanish whenever the modulus is even. -/
theorem paper_fold_multiplicity_spectrum_blindspot_half (m : ℕ)
    (hEven : Even (foldMultiplicityModulus m)) :
    foldMultiplicityFourierAtHalfModulus m = 0 := by
  exact paper_fold_spectrum_parity_zero m hEven

end Omega.Folding
