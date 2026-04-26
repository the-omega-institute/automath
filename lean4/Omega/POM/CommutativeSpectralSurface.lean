import Omega.POM.BivariateMomentZetaFredholm
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete quotient-algebra data for the commutative spectral-surface wrapper. -/
structure PomCommutativeSpectralSurfaceData where
  A : Type*
  instCommRingA : CommRing A
  zCoord : A
  uCoord : A
  quotientGenerator : A
  clearedDenominator : MvPolynomial (Fin 2) ℤ
  quotientRelation :
    MvPolynomial.eval₂ (Int.castRingHom A)
      (fun i => if i = 0 then zCoord else uCoord) clearedDenominator = 0

attribute [instance] PomCommutativeSpectralSurfaceData.instCommRingA

namespace PomCommutativeSpectralSurfaceData

/-- Coordinate multiplication in the `z`-direction. -/
def pom_commutative_spectral_surface_zShift (D : PomCommutativeSpectralSurfaceData) : D.A → D.A :=
  fun a => D.zCoord * a

/-- Coordinate multiplication in the `u`-direction. -/
def pom_commutative_spectral_surface_uShift (D : PomCommutativeSpectralSurfaceData) : D.A → D.A :=
  fun a => D.uCoord * a

/-- Concrete trace-expansion proposition extracted from the quotient relation. -/
def pom_commutative_spectral_surface_traceExpansion
    (D : PomCommutativeSpectralSurfaceData) : Prop :=
  MvPolynomial.eval₂ (Int.castRingHom D.A)
      (fun i => if i = 0 then D.zCoord else D.uCoord) D.clearedDenominator =
    0

/-- Rational Fredholm witness: in this wrapper it is the same cleared-denominator identity. -/
def pom_commutative_spectral_surface_fredholmDetRational
    (D : PomCommutativeSpectralSurfaceData) : Prop :=
  D.pom_commutative_spectral_surface_traceExpansion

/-- Quotient-algebra coordinate readout for the `z`-shift. -/
def pom_commutative_spectral_surface_coefficientRecovery
    (D : PomCommutativeSpectralSurfaceData) : Prop :=
  D.pom_commutative_spectral_surface_zShift D.quotientGenerator = D.zCoord * D.quotientGenerator

/-- Paper-facing spectral-surface package: the cleared denominator cuts out the quotient relation,
and the `z`- and `u`-shifts are the commuting coordinate multiplications. -/
def holds (D : PomCommutativeSpectralSurfaceData) : Prop :=
  (D.pom_commutative_spectral_surface_fredholmDetRational ∧
      D.pom_commutative_spectral_surface_coefficientRecovery) ∧
    D.pom_commutative_spectral_surface_uShift D.quotientGenerator = D.uCoord * D.quotientGenerator ∧
    Function.Commute D.pom_commutative_spectral_surface_zShift
      D.pom_commutative_spectral_surface_uShift ∧
    ∀ a : D.A,
      D.pom_commutative_spectral_surface_zShift (D.pom_commutative_spectral_surface_uShift a) =
        D.pom_commutative_spectral_surface_uShift (D.pom_commutative_spectral_surface_zShift a)

end PomCommutativeSpectralSurfaceData

open PomCommutativeSpectralSurfaceData

/-- Paper label: `thm:pom-commutative-spectral-surface`. -/
theorem paper_pom_commutative_spectral_surface (D : PomCommutativeSpectralSurfaceData) : D.holds := by
  have hFredholm :
      D.pom_commutative_spectral_surface_traceExpansion →
        D.pom_commutative_spectral_surface_fredholmDetRational := fun h => h
  have hCoeff :
      D.pom_commutative_spectral_surface_fredholmDetRational →
        D.pom_commutative_spectral_surface_coefficientRecovery := by
    intro hRational
    rfl
  have hWrapper :=
    paper_pom_bivariate_moment_zeta_fredholm
      (traceExpansion := D.pom_commutative_spectral_surface_traceExpansion)
      (fredholmDetRational := D.pom_commutative_spectral_surface_fredholmDetRational)
      (coefficientRecovery := D.pom_commutative_spectral_surface_coefficientRecovery)
      hFredholm hCoeff
  refine ⟨?_, rfl, ?_, ?_⟩
  · simpa [PomCommutativeSpectralSurfaceData.pom_commutative_spectral_surface_traceExpansion] using
      hWrapper D.quotientRelation
  · intro a
    simp [PomCommutativeSpectralSurfaceData.pom_commutative_spectral_surface_zShift,
      PomCommutativeSpectralSurfaceData.pom_commutative_spectral_surface_uShift, mul_left_comm,
      mul_comm]
  · intro a
    simp [PomCommutativeSpectralSurfaceData.pom_commutative_spectral_surface_zShift,
      PomCommutativeSpectralSurfaceData.pom_commutative_spectral_surface_uShift, mul_left_comm,
      mul_comm]

end Omega.POM
