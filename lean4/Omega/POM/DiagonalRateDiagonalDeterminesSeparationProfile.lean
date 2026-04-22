import Mathlib.Tactic
import Omega.POM.DiagonalRateDiagonalStatisticsComplete
import Omega.POM.DiagonalRateSeparationSpectralResidue

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-diagonal-rate-diagonal-determines-separation-profile`. -/
theorem paper_pom_diagonal_rate_diagonal_determines_separation_profile
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ δ : ℚ) (t : α → ℚ) (anchor : α) (hanchor : t anchor = 1)
    (hp_nonzero : ∀ x, diagonalStatistic κ t x ≠ 0)
    (n : ℕ) (sep : ℕ → ℝ) (lambda weight spectralRoot : Fin n → ℝ)
    (κr δr tx th : ℝ) (numeratorEval denominatorDerivativeEval : Fin n → ℝ)
    (hlambda : Function.Injective lambda)
    (hsum : (∑ i, weight i) = 1)
    (hexpansion : ∀ m, sep m = ∑ i, weight i * (lambda i) ^ m)
    (hresidue :
      ∀ i,
        weight i =
          ((1 + κr) / (1 + κr * δr)) * (tx - κr) * (th - κr) *
            (numeratorEval i / denominatorDerivativeEval i))
    (hunique :
      ∀ otherWeight : Fin n → ℝ,
        (∀ m, sep m = ∑ i, otherWeight i * (lambda i) ^ m) → otherWeight = weight) :
    let p := diagonalStatistic κ t
    κ = p anchor - 1 ∧
      (∀ x, t x = p anchor / p x) ∧
      (∀ x y, diagonalKernel κ δ t x y = if x = y then p x else δ * diagonalStationary κ t y) ∧
      (∑ i, weight i) = 1 ∧
      (∀ m, sep m = ∑ i, weight i * (lambda i) ^ m) ∧
      (∀ i,
        weight i =
          ((1 + κr) / (1 + κr * δr)) * (tx - κr) * (th - κr) *
            (numeratorEval i / denominatorDerivativeEval i)) ∧
      ∀ otherWeight : Fin n → ℝ,
        (∀ m, sep m = ∑ i, otherWeight i * (lambda i) ^ m) → otherWeight = weight := by
  let H : DiagonalRateSeparationSpectralResidueData := {
    n := n
    sep := sep
    lambda := lambda
    weight := weight
    spectralRoot := spectralRoot
    kappa := κr
    delta := δr
    tx := tx
    th := th
    numeratorEval := numeratorEval
    denominatorDerivativeEval := denominatorDerivativeEval
    lambdaDistinct := hlambda
    weights_sum_to_one_witness := hsum
    spectralExpansion_witness := hexpansion
    residueClosedForm_witness := hresidue
    uniqueWeights_witness := hunique
  }
  have hdiag := paper_pom_diagonal_rate_diagonal_statistics_complete (α := α) κ δ t
  rcases hdiag with ⟨hp, _hanti, _hroot, _huniqRoot, _hξ, _hw, _hπ, _hfactor, hkernel⟩
  have hAnchorValue : diagonalStatistic κ t anchor = 1 + κ := by
    simp [diagonalStatistic, hanchor]
  have hκ : κ = diagonalStatistic κ t anchor - 1 := by
    linarith
  have hrecover :
      ∀ x, t x = diagonalStatistic κ t anchor / diagonalStatistic κ t x := by
    intro x
    have ht : t x ≠ 0 := by
      intro htx
      apply hp_nonzero x
      simp [diagonalStatistic, htx]
    have hmul : t x * diagonalStatistic κ t x = 1 + κ := by
      rw [hp x]
      field_simp [ht]
    calc
      t x = (1 + κ) / diagonalStatistic κ t x := by
        exact (eq_div_iff (hp_nonzero x)).2 (by simpa [mul_comm] using hmul)
      _ = diagonalStatistic κ t anchor / diagonalStatistic κ t x := by
        simp [hAnchorValue]
  have hprofile := paper_pom_diagonal_rate_separation_spectral_residue H
  refine ⟨hκ, hrecover, hkernel, hprofile.1, hprofile.2.1, hprofile.2.2.1, hprofile.2.2.2⟩

end Omega.POM
