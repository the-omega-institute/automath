import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Omega.EA.Z2x2JointSpectralMeasure

namespace Omega.EA

open Polynomial
open scoped BigOperators

noncomputable section

/-- The sectorwise power sums determined by the block-size function `d`. -/
def sectorPowerSumFromBlockSizes (d : Z2x2Character → Nat) (χ : Z2x2Character) (k : Nat) : ℚ :=
  (d χ : ℚ) ^ k

/-- Fourier-Hadamard inversion of the `q = 0` signed moment recovers the underlying block size. -/
def recoverSectorBlockSizeFromSignedMoments
    (m : Nat) (d : Z2x2Character → Nat) (χ : Z2x2Character) : ℚ :=
  (1 / 4 : ℚ) *
    ∑ s : Fin 2, ∑ t : Fin 2,
      scanEigenvalue χ ^ (s : Nat) * revEigenvalue χ ^ (t : Nat) *
        ((2 ^ m : ℚ) * signedMomentTrace m d s t 0)

/-- The recovered power sums are the powers of the recovered sector size. -/
def recoverSectorPowerSumFromSignedMoments
    (m : Nat) (d : Z2x2Character → Nat) (χ : Z2x2Character) (k : Nat) : ℚ :=
  recoverSectorBlockSizeFromSignedMoments m d χ ^ k

/-- Newton's identities are tautological for the monic linear sector polynomial. -/
def sectorPolynomialFromBlockSizes (d : Z2x2Character → Nat) (χ : Z2x2Character) : Polynomial ℚ :=
  X - C (sectorPowerSumFromBlockSizes d χ 1)

/-- The sector polynomial reconstructed from the recovered signed power sums. -/
def recoverSectorPolynomialFromSignedMoments
    (m : Nat) (d : Z2x2Character → Nat) (χ : Z2x2Character) : Polynomial ℚ :=
  X - C (recoverSectorPowerSumFromSignedMoments m d χ 1)

private theorem recoverSectorBlockSizeFromSignedMoments_eq
    (m : Nat) (d : Z2x2Character → Nat) (hmass : Finset.univ.sum d = 2 ^ m)
    (χ : Z2x2Character) :
    recoverSectorBlockSizeFromSignedMoments m d χ = sectorPowerSumFromBlockSizes d χ 1 := by
  have hpow_ne : (2 ^ m : ℚ) ≠ 0 := by positivity
  have _ := paper_fold_groupoid_z2x2_joint_spectral_measure m d hmass
  cases χ with
  | mk a b =>
      cases a <;> cases b <;>
        simp [recoverSectorBlockSizeFromSignedMoments, signedMomentTrace, normalizedBlockTrace,
          sectorPowerSumFromBlockSizes, scanEigenvalue, revEigenvalue, signOfBool,
          Fintype.sum_prod_type, Fin.sum_univ_two, div_eq_mul_inv] <;>
        field_simp [hpow_ne] <;>
        ring

/-- Paper label: `prop:fold-chi-layered-fiber-spectrum-certified-by-signed-powersums`. The
Fourier-Hadamard inversion recovers each `χ`-sector block size from the four signed moments, and
the monic linear Newton identity turns that recovered power sum into the sector polynomial. -/
theorem paper_fold_chi_layered_fiber_spectrum_certified_by_signed_powersums
    (m : Nat) (d : Omega.EA.Z2x2Character → Nat) (hmass : Finset.univ.sum d = 2 ^ m) :
    ∀ chi : Omega.EA.Z2x2Character,
      sectorPolynomialFromBlockSizes d chi = recoverSectorPolynomialFromSignedMoments m d chi := by
  intro chi
  simp [sectorPolynomialFromBlockSizes, recoverSectorPolynomialFromSignedMoments,
    recoverSectorPowerSumFromSignedMoments, recoverSectorBlockSizeFromSignedMoments_eq m d hmass chi]

end

end Omega.EA
