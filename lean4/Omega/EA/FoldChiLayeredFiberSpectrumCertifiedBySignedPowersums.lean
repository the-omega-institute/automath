import Mathlib.Tactic
import Omega.EA.Z2x2JointSpectralMeasure

namespace Omega.EA

open scoped BigOperators

/-- Concrete package for recovering the `χ`-sector power sums and the corresponding sector
polynomial coefficients from the signed power sums on `{±1}²`. The Newton step is recorded by an
explicit linear kernel on the first `rootCount` power sums. -/
structure FoldChiLayeredFiberSpectrumData where
  rootCount : ℕ
  sectorMultiplicity : Z2x2Character → Fin rootCount → ℕ
  fiberWeight : Fin rootCount → ℚ
  newtonKernel : Fin rootCount → Fin rootCount → ℚ
  sectorCoeff : Z2x2Character → Fin rootCount → ℚ
  coeff_from_power_sums :
    ∀ χ i,
      sectorCoeff χ i =
        ∑ q : Fin rootCount,
          newtonKernel i q *
            (∑ j : Fin rootCount,
              (sectorMultiplicity χ j : ℚ) * fiberWeight j ^ (q.val + 1))

namespace FoldChiLayeredFiberSpectrumData

/-- Sectorwise power sum sequence. -/
def sectorPowerSum (D : FoldChiLayeredFiberSpectrumData) (χ : Z2x2Character) (k : ℕ) : ℚ :=
  ∑ j : Fin D.rootCount, (D.sectorMultiplicity χ j : ℚ) * D.fiberWeight j ^ k

/-- Signed power sum family indexed by the two Walsh signs and the power-sum order. -/
def signedPowerSum
    (D : FoldChiLayeredFiberSpectrumData) (s t : Fin 2) (q : Fin D.rootCount) : ℚ :=
  ∑ χ : Z2x2Character,
    scanEigenvalue χ ^ (s : ℕ) * revEigenvalue χ ^ (t : ℕ) *
      D.sectorPowerSum χ (q.val + 1)

/-- Fourier-Hadamard inversion recovering one sector power sum from the four signed moments. -/
def hadamardRecoveredPowerSum
    (D : FoldChiLayeredFiberSpectrumData) (χ : Z2x2Character) (q : Fin D.rootCount) : ℚ :=
  (1 / 4 : ℚ) *
    ∑ s : Fin 2, ∑ t : Fin 2,
      scanEigenvalue χ ^ (s : ℕ) * revEigenvalue χ ^ (t : ℕ) * D.signedPowerSum s t q

/-- Newton reconstruction of one sector coefficient from the recovered power sums. -/
def recoveredCoeff
    (D : FoldChiLayeredFiberSpectrumData) (χ : Z2x2Character) (i : Fin D.rootCount) : ℚ :=
  ∑ q : Fin D.rootCount, D.newtonKernel i q * D.hadamardRecoveredPowerSum χ q

/-- All sector power sums are recovered by Fourier-Hadamard inversion, and then the coefficient
kernel recovers the sector polynomial coefficients from those power sums. -/
def sectorPolynomialsRecoverable (D : FoldChiLayeredFiberSpectrumData) : Prop :=
  (∀ χ : Z2x2Character, ∀ q : Fin D.rootCount,
      D.hadamardRecoveredPowerSum χ q = D.sectorPowerSum χ (q.val + 1)) ∧
    ∀ χ : Z2x2Character, ∀ i : Fin D.rootCount, D.recoveredCoeff χ i = D.sectorCoeff χ i

private theorem hadamardRecoveredPowerSum_eq
    (D : FoldChiLayeredFiberSpectrumData) (χ : Z2x2Character) (q : Fin D.rootCount) :
    D.hadamardRecoveredPowerSum χ q = D.sectorPowerSum χ (q.val + 1) := by
  cases χ with
  | mk a b =>
      cases a <;> cases b <;>
        simp [FoldChiLayeredFiberSpectrumData.hadamardRecoveredPowerSum,
          FoldChiLayeredFiberSpectrumData.signedPowerSum,
          FoldChiLayeredFiberSpectrumData.sectorPowerSum, scanEigenvalue, revEigenvalue,
          signOfBool, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        ring_nf

/-- Paper label: `prop:fold-chi-layered-fiber-spectrum-certified-by-signed-powersums`. The four
signed moment channels recover each `χ`-sector power-sum sequence by the Walsh-Hadamard inverse on
`{±1}²`, and the recorded Newton kernel then reconstructs the sector polynomial coefficients from
the first `|X_m|` power sums. -/
theorem paper_fold_chi_layered_fiber_spectrum_certified_by_signed_powersums
    (D : FoldChiLayeredFiberSpectrumData) : D.sectorPolynomialsRecoverable := by
  refine ⟨?_, ?_⟩
  · intro χ q
    exact hadamardRecoveredPowerSum_eq D χ q
  · intro χ i
    simp [FoldChiLayeredFiberSpectrumData.recoveredCoeff,
      FoldChiLayeredFiberSpectrumData.coeff_from_power_sums,
      FoldChiLayeredFiberSpectrumData.sectorPowerSum, hadamardRecoveredPowerSum_eq]

end FoldChiLayeredFiberSpectrumData

end Omega.EA
