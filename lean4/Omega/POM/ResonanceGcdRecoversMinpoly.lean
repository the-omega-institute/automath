import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullIntegralPrincipalization

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite Hankel-null gcd recovery data. The basis vectors lie in the resonance null
kernel, principalization identifies that kernel with the minimal-polynomial multiple module, and
the recorded Bezout combination contains the minimal polynomial. -/
structure pom_resonance_gcd_recovers_minpoly_data where
  principalization : ResonanceHankelNullIntegralPrincipalizationData
  basisRank : ℕ
  basisVector : Fin basisRank → Fin principalization.n → ℤ
  annihilator : Fin basisRank → Polynomial ℤ
  minpoly : Polynomial ℤ
  commonDivisor : Polynomial ℤ
  bezoutCoeff : Fin basisRank → Polynomial ℤ
  basisVector_mem : ∀ j, basisVector j ∈ principalization.nullModeKernel
  basis_annihilator_of_multiple :
    ∀ j, basisVector j ∈ principalization.multipleModule → minpoly ∣ annihilator j
  commonDivisor_dvd_annihilator : ∀ j, commonDivisor ∣ annihilator j
  commonDivisor_greatest :
    ∀ C : Polynomial ℤ, (∀ j, C ∣ annihilator j) → C ∣ commonDivisor
  bezout_minpoly : (∑ j : Fin basisRank, bezoutCoeff j * annihilator j) = minpoly
  commonDivisor_eq_sign :
    minpoly ∣ commonDivisor → commonDivisor ∣ minpoly →
      commonDivisor = minpoly ∨ commonDivisor = -minpoly

/-- The finite Hankel-null basis has gcd equal to the normalized minimal polynomial up to sign. -/
def pom_resonance_gcd_recovers_minpoly_statement
    (D : pom_resonance_gcd_recovers_minpoly_data) : Prop :=
  D.commonDivisor = D.minpoly ∨ D.commonDivisor = -D.minpoly

/-- Paper label: `cor:pom-resonance-gcd-recovers-minpoly`. -/
theorem paper_pom_resonance_gcd_recovers_minpoly
    (D : pom_resonance_gcd_recovers_minpoly_data) :
    pom_resonance_gcd_recovers_minpoly_statement D := by
  have hPrincipal : D.principalization.nullModesEqMultiples :=
    paper_pom_resonance_hankel_null_integral_principalization D.principalization
  have hPrincipalEq :
      D.principalization.nullModeKernel = D.principalization.multipleModule :=
    hPrincipal
  have hMinpolyDvdAnnihilator : ∀ j, D.minpoly ∣ D.annihilator j := by
    intro j
    have hMultiple : D.basisVector j ∈ D.principalization.multipleModule := by
      simpa [hPrincipalEq] using D.basisVector_mem j
    exact D.basis_annihilator_of_multiple j hMultiple
  have hMinpolyDvdCommon : D.minpoly ∣ D.commonDivisor :=
    D.commonDivisor_greatest D.minpoly hMinpolyDvdAnnihilator
  have hCommonDvdMinpoly : D.commonDivisor ∣ D.minpoly := by
    rw [← D.bezout_minpoly]
    exact Finset.dvd_sum fun j _ =>
      dvd_mul_of_dvd_right (D.commonDivisor_dvd_annihilator j) (D.bezoutCoeff j)
  exact D.commonDivisor_eq_sign hMinpolyDvdCommon hCommonDvdMinpoly

end Omega.POM
