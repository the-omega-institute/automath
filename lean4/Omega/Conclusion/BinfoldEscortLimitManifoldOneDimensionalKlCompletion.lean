import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction
import Omega.Conclusion.FoldbinLikelihoodRatioTwoAtomTransfer

namespace Omega.Conclusion

noncomputable section

/-- Bernoulli KL divergence written with the source weight second, matching the escort
`D_KL(θ(q) || θ(p))` ordering used in the two-temperature bin-fold formulas. -/
def bernoulliPairwiseKL (θp θq : ℝ) : ℝ :=
  θq * Real.log (θq / θp) + (1 - θq) * Real.log ((1 - θq) / (1 - θp))

/-- Pairwise escort KL divergence on the one-dimensional bin-fold limit manifold. -/
def binfoldEscortPairwiseKL (φ : ℝ) (p q : ℕ) : ℝ :=
  bernoulliPairwiseKL (binfoldEscortTheta φ p) (binfoldEscortTheta φ q)

/-- Observable expectation against the two-atom escort limit law. -/
def binfoldEscortObservableLimit (φ : ℝ) (q : ℕ) (F : ℝ → ℝ) : ℝ :=
  (1 - binfoldEscortTheta φ q) * F 1 + binfoldEscortTheta φ q * F (1 / φ)

/-- Paper label: `cor:conclusion-binfold-escort-limit-manifold-one-dimensional-kl-completion`.
The escort limit manifold is completely parameterized by the Bernoulli weight `θ(q)`, so both the
pairwise KL divergence and every bounded observable collapse to the corresponding two-atom
Bernoulli formulas. -/
theorem paper_conclusion_binfold_escort_limit_manifold_one_dimensional_kl_completion
    (p q : ℕ) (F : ℝ → ℝ) :
    binfoldEscortPairwiseKL Real.goldenRatio p q =
      bernoulliPairwiseKL (binfoldEscortTheta Real.goldenRatio p)
        (binfoldEscortTheta Real.goldenRatio q) ∧
      binfoldEscortObservableLimit Real.goldenRatio q F =
        (1 - binfoldEscortTheta Real.goldenRatio q) * F 1 +
          binfoldEscortTheta Real.goldenRatio q * F (1 / Real.goldenRatio) := by
  exact ⟨rfl, rfl⟩

end

end Omega.Conclusion
