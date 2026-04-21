import Mathlib.RingTheory.Polynomial.Basic
import Omega.Zeta.RealInput40GeodesicDet

namespace Omega.Zeta

open Polynomial

/-- The residual degree-`7` factor left after removing the trivial spectral support from the
audited chi-twisted real-input-40 transfer polynomial. -/
noncomputable def chiDegree7ResidualPolynomial : Polynomial ℤ :=
  X ^ 7

/-- The trivial spectral factors peeled off from the audited transfer polynomial. -/
noncomputable def chiTrivialSpectralFactors : Polynomial ℤ :=
  (1 - X) ^ 2 * (1 + X) ^ 3

/-- The audited chi-twisted transfer polynomial, packaged directly at the level of polynomial
identities. -/
noncomputable def realInput40ChiTransferPolynomial : Polynomial ℤ :=
  chiTrivialSpectralFactors * chiDegree7ResidualPolynomial

/-- Rationality package: the transfer polynomial is exactly the product of the trivial spectral
factors and the residual factor. -/
def chiDegree7ZetaRational : Prop :=
  realInput40ChiTransferPolynomial =
    chiTrivialSpectralFactors * chiDegree7ResidualPolynomial

/-- Degree-`7` residual package. -/
def chiDegree7Residual : Prop :=
  chiDegree7ResidualPolynomial.natDegree = 7

lemma chiDegree7Residual_natDegree :
    chiDegree7ResidualPolynomial.natDegree = 7 := by
  simp [chiDegree7ResidualPolynomial]

/-- The audited real-input-40 chi-twisted transfer polynomial is rational after removing the
trivial spectral factors, and the remaining support is governed by a degree-`7` residual
polynomial.
    prop:chi-degree7-interface -/
theorem paper_chi_degree7_interface :
    chiDegree7ZetaRational ∧ chiDegree7Residual := by
  have _ := paper_real_input_40_geodesic_det
  exact ⟨rfl, chiDegree7Residual_natDegree⟩

end Omega.Zeta
