import Omega.Zeta.DynZeta

namespace Omega.Zeta

/-- Publication-facing wrapper for
`prop:finite-zeta-imaginary-periodicity`
in `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`. -/
theorem paper_etds_finite_zeta_imaginary_periodicity :
    (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
    (fredholmGoldenMean 0).det = 1 ∧
    (fredholmGoldenMean 1).det = -1 ∧
    (fredholmGoldenMean (-1)).det = 1 :=
  paper_finite_zeta_periodicity_witness

end Omega.Zeta
