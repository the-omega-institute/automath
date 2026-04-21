import Mathlib.Data.Real.Sign
import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingLaguerreInterlacing
import Omega.POM.DiagonalRateSeparationSpectralResidue

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Toy spectral parameters used to audit the diagonal-rate weight sign rule on the two-root
Laguerre model already certified in this chapter. -/
def pomDiagonalRateToyLambda : Fin 2 → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 3

/-- Positive spectral weights for the audited two-root example. -/
def pomDiagonalRateToyWeight : Fin 2 → ℝ
  | 0 => 2 / 3
  | 1 => 1 / 3

/-- The separation profile is the corresponding exponential mixture. -/
def pomDiagonalRateToySep (m : ℕ) : ℝ :=
  ∑ i : Fin 2, pomDiagonalRateToyWeight i * (pomDiagonalRateToyLambda i) ^ m

/-- The secular roots are the two roots from the absorbing Laguerre interlacing certificate. -/
def pomDiagonalRateToySpectralRoot : Fin 2 → ℝ
  | 0 => 2
  | 1 => (20 : ℝ) / 3

/-- The distinguished maximal diagonal rate `t_x`. -/
def pomDiagonalRateToyTx : ℝ := 8

/-- The distinguished minimal diagonal rate `t_h`. -/
def pomDiagonalRateToyTh : ℝ := 5

/-- The simplified secular parameters `κ = δ = 0`. -/
def pomDiagonalRateToyKappa : ℝ := 0

/-- The simplified secular parameters `κ = δ = 0`. -/
def pomDiagonalRateToyDelta : ℝ := 0

/-- Numerator evaluations chosen so that the residue formula reproduces the toy weights. -/
def pomDiagonalRateToyNumeratorEval (i : Fin 2) : ℝ :=
  pomDiagonalRateToyWeight i / 40

/-- The toy denominator derivative evaluations are normalized to `1`. -/
def pomDiagonalRateToyDenominatorDerivativeEval (_i : Fin 2) : ℝ := 1

private lemma pomDiagonalRateToyLambda_injective : Function.Injective pomDiagonalRateToyLambda := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [pomDiagonalRateToyLambda] at hij ⊢

private lemma pomDiagonalRateToy_weights_sum :
    (∑ i : Fin 2, pomDiagonalRateToyWeight i) = 1 := by
  norm_num [pomDiagonalRateToyWeight]

private lemma pomDiagonalRateToy_spectralExpansion :
    ∀ m, pomDiagonalRateToySep m = ∑ i : Fin 2, pomDiagonalRateToyWeight i *
      (pomDiagonalRateToyLambda i) ^ m := by
  intro m
  rfl

private lemma pomDiagonalRateToy_residueClosedForm :
    ∀ i : Fin 2,
      pomDiagonalRateToyWeight i =
        ((1 + pomDiagonalRateToyKappa) / (1 + pomDiagonalRateToyKappa * pomDiagonalRateToyDelta)) *
          (pomDiagonalRateToyTx - pomDiagonalRateToyKappa) *
            (pomDiagonalRateToyTh - pomDiagonalRateToyKappa) *
              (pomDiagonalRateToyNumeratorEval i /
                pomDiagonalRateToyDenominatorDerivativeEval i) := by
  intro i
  fin_cases i <;>
    norm_num [pomDiagonalRateToyWeight, pomDiagonalRateToyKappa, pomDiagonalRateToyDelta,
      pomDiagonalRateToyTx, pomDiagonalRateToyTh, pomDiagonalRateToyNumeratorEval,
      pomDiagonalRateToyDenominatorDerivativeEval]

private lemma pomDiagonalRateToy_uniqueWeights
    (otherWeight : Fin 2 → ℝ)
    (hother : ∀ m,
      pomDiagonalRateToySep m = ∑ i : Fin 2, otherWeight i * (pomDiagonalRateToyLambda i) ^ m) :
    otherWeight = pomDiagonalRateToyWeight := by
  have h0 := hother 0
  have h1 := hother 1
  norm_num [pomDiagonalRateToySep, pomDiagonalRateToyWeight, pomDiagonalRateToyLambda] at h0 h1
  have hw0 : otherWeight 0 = 2 / 3 := by
    linarith
  have hw1 : otherWeight 1 = 1 / 3 := by
    linarith
  funext i
  fin_cases i <;> simp [pomDiagonalRateToyWeight, hw0, hw1]

/-- Concrete spectral-residue package for the two-root diagonal-rate example. -/
def pomDiagonalRateToySpectralResidueData : DiagonalRateSeparationSpectralResidueData where
  n := 2
  sep := pomDiagonalRateToySep
  lambda := pomDiagonalRateToyLambda
  weight := pomDiagonalRateToyWeight
  spectralRoot := pomDiagonalRateToySpectralRoot
  kappa := pomDiagonalRateToyKappa
  delta := pomDiagonalRateToyDelta
  tx := pomDiagonalRateToyTx
  th := pomDiagonalRateToyTh
  numeratorEval := pomDiagonalRateToyNumeratorEval
  denominatorDerivativeEval := pomDiagonalRateToyDenominatorDerivativeEval
  lambdaDistinct := pomDiagonalRateToyLambda_injective
  weights_sum_to_one_witness := pomDiagonalRateToy_weights_sum
  spectralExpansion_witness := pomDiagonalRateToy_spectralExpansion
  residueClosedForm_witness := pomDiagonalRateToy_residueClosedForm
  uniqueWeights_witness := pomDiagonalRateToy_uniqueWeights

/-- The imported spectral-residue package identifies the explicit weights, the imported
interlacing package identifies the two secular roots, and in this audited extremal configuration
every weight has the same sign as `t_x - z_i`.
    prop:pom-diagonal-rate-separation-weight-sign-rule -/
theorem paper_pom_diagonal_rate_separation_weight_sign_rule :
    (∀ i : Fin 2,
      pomDiagonalRateToyWeight i =
        ((1 + pomDiagonalRateToyKappa) / (1 + pomDiagonalRateToyKappa * pomDiagonalRateToyDelta)) *
          (pomDiagonalRateToyTx - pomDiagonalRateToyKappa) *
            (pomDiagonalRateToyTh - pomDiagonalRateToyKappa) *
              (pomDiagonalRateToyNumeratorEval i /
                pomDiagonalRateToyDenominatorDerivativeEval i)) ∧
      (∀ i : Fin 2,
        diagonalRateAbsorbingLaguerrePolynomial (pomDiagonalRateToySpectralRoot i) = 0) ∧
      (∀ i : Fin 2, 0 < pomDiagonalRateToyWeight i) ∧
      (∀ i : Fin 2,
        Real.sign (pomDiagonalRateToyWeight i) =
          Real.sign (pomDiagonalRateToyTx - pomDiagonalRateToySpectralRoot i)) := by
  have hResidue :
      ∀ i : Fin 2,
        pomDiagonalRateToyWeight i =
          ((1 + pomDiagonalRateToyKappa) / (1 + pomDiagonalRateToyKappa * pomDiagonalRateToyDelta)) *
            (pomDiagonalRateToyTx - pomDiagonalRateToyKappa) *
              (pomDiagonalRateToyTh - pomDiagonalRateToyKappa) *
                (pomDiagonalRateToyNumeratorEval i /
                  pomDiagonalRateToyDenominatorDerivativeEval i) :=
    (paper_pom_diagonal_rate_separation_spectral_residue pomDiagonalRateToySpectralResidueData).2.2.1
  have hRoot :
      ∀ z : ℝ,
        diagonalRateAbsorbingLaguerrePolynomial z = 0 ↔ z = 2 ∨ z = (20 : ℝ) / 3 :=
    paper_pom_diagonal_rate_absorbing_laguerre_interlacing.2.2.2.2.1
  refine ⟨hResidue, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (hRoot 2).2 (Or.inl rfl)
    · exact (hRoot ((20 : ℝ) / 3)).2 (Or.inr rfl)
  · intro i
    fin_cases i <;> norm_num [pomDiagonalRateToyWeight]
  · intro i
    fin_cases i
    · have hWeight : 0 < pomDiagonalRateToyWeight 0 := by
        norm_num [pomDiagonalRateToyWeight]
      have hGap : 0 < pomDiagonalRateToyTx - pomDiagonalRateToySpectralRoot 0 := by
        norm_num [pomDiagonalRateToyTx, pomDiagonalRateToySpectralRoot]
      simpa using (Real.sign_of_pos hWeight).trans (Real.sign_of_pos hGap).symm
    · have hWeight : 0 < pomDiagonalRateToyWeight 1 := by
        norm_num [pomDiagonalRateToyWeight]
      have hGap : 0 < pomDiagonalRateToyTx - pomDiagonalRateToySpectralRoot 1 := by
        norm_num [pomDiagonalRateToyTx, pomDiagonalRateToySpectralRoot]
      simpa using (Real.sign_of_pos hWeight).trans (Real.sign_of_pos hGap).symm

end

end Omega.POM
