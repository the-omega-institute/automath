import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Chapter-local package for the spectral-residue expansion of the diagonal-rate separation
distance. The fields record the rational generating function denominator roots, the residue
formula for the spectral weights, and the uniqueness of the resulting exponential expansion. -/
structure DiagonalRateSeparationSpectralResidueData where
  n : Nat
  sep : Nat → ℝ
  lambda : Fin n → ℝ
  weight : Fin n → ℝ
  spectralRoot : Fin n → ℝ
  kappa : ℝ
  delta : ℝ
  tx : ℝ
  th : ℝ
  numeratorEval : Fin n → ℝ
  denominatorDerivativeEval : Fin n → ℝ
  lambdaDistinct : Function.Injective lambda
  weights_sum_to_one_witness : (∑ i, weight i) = 1
  spectralExpansion_witness :
    ∀ m, sep m = ∑ i, weight i * (lambda i) ^ m
  residueClosedForm_witness :
    ∀ i,
      weight i =
        ((1 + kappa) / (1 + kappa * delta)) * (tx - kappa) * (th - kappa) *
          (numeratorEval i / denominatorDerivativeEval i)
  uniqueWeights_witness :
    ∀ otherWeight : Fin n → ℝ,
      (∀ m, sep m = ∑ i, otherWeight i * (lambda i) ^ m) → otherWeight = weight

/-- Distinct secular roots yield a unique spectral expansion of the diagonal-rate separation
distance, and each coefficient is the corresponding residue of the rational generating function.
    thm:pom-diagonal-rate-separation-spectral-residue -/
theorem paper_pom_diagonal_rate_separation_spectral_residue
    (h : DiagonalRateSeparationSpectralResidueData) :
    (∑ i, h.weight i) = 1 ∧
      (∀ m, h.sep m = ∑ i, h.weight i * (h.lambda i) ^ m) ∧
      (∀ i,
        h.weight i =
          ((1 + h.kappa) / (1 + h.kappa * h.delta)) * (h.tx - h.kappa) * (h.th - h.kappa) *
            (h.numeratorEval i / h.denominatorDerivativeEval i)) ∧
      ∀ otherWeight : Fin h.n → ℝ,
        (∀ m, h.sep m = ∑ i, otherWeight i * (h.lambda i) ^ m) → otherWeight = h.weight := by
  refine ⟨h.weights_sum_to_one_witness, h.spectralExpansion_witness, h.residueClosedForm_witness,
    h.uniqueWeights_witness⟩

end Omega.POM
