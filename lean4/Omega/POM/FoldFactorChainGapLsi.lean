import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FoldFactorChainDerivedInvariants

namespace Omega.POM

/-- Concrete data for comparing the compressed fold-factor chain with its fiber-constant
hypercube lift. The variance, entropy, and Dirichlet form identities record that fiber-constant
lifts preserve the relevant test-function functionals, while the two hypercube inequalities are
the baseline spectral-gap and logarithmic-Sobolev bounds to be pushed down to the factor chain. -/
structure FoldFactorChainGapLsiData where
  m : ℕ
  hm : 1 ≤ m
  compressedVariance : ℝ
  liftedVariance : ℝ
  compressedEntropy : ℝ
  liftedEntropy : ℝ
  compressedDirichlet : ℝ
  liftedDirichlet : ℝ
  variance_of_fiberConstantLift : compressedVariance = liftedVariance
  entropy_of_fiberConstantLift : compressedEntropy = liftedEntropy
  dirichlet_of_fiberConstantLift : compressedDirichlet = liftedDirichlet
  lifted_gap_bound : foldFactorChainGapLower m * liftedVariance ≤ liftedDirichlet
  lifted_lsi_bound : foldFactorChainLogSobolevLower m * liftedEntropy ≤ liftedDirichlet

namespace FoldFactorChainGapLsiData

/-- The pushed-down spectral-gap lower bound for the compressed factor chain. -/
def compressedGapLowerBound (D : FoldFactorChainGapLsiData) : Prop :=
  foldFactorChainGapLower D.m * D.compressedVariance ≤ D.compressedDirichlet

/-- The pushed-down logarithmic-Sobolev lower bound for the compressed factor chain. -/
def compressedLsiLowerBound (D : FoldFactorChainGapLsiData) : Prop :=
  foldFactorChainLogSobolevLower D.m * D.compressedEntropy ≤ D.compressedDirichlet

/-- Combined paper-facing package: the compressed fold-factor chain inherits both lower bounds
from the hypercube lift. -/
def gap_lsi_statement (D : FoldFactorChainGapLsiData) : Prop :=
  D.compressedGapLowerBound ∧ D.compressedLsiLowerBound

lemma compressedGapLowerBound_proof (D : FoldFactorChainGapLsiData) :
    D.compressedGapLowerBound := by
  unfold compressedGapLowerBound
  rw [D.variance_of_fiberConstantLift, D.dirichlet_of_fiberConstantLift]
  exact D.lifted_gap_bound

lemma compressedLsiLowerBound_proof (D : FoldFactorChainGapLsiData) :
    D.compressedLsiLowerBound := by
  unfold compressedLsiLowerBound
  rw [D.entropy_of_fiberConstantLift, D.dirichlet_of_fiberConstantLift]
  exact D.lifted_lsi_bound

end FoldFactorChainGapLsiData

/-- Paper label: `thm:pom-fold-factor-chain-gap-lsi`.
For fiber-constant lifts, the variance, entropy, and Dirichlet form agree with their hypercube
counterparts, so the hypercube spectral-gap and logarithmic-Sobolev lower bounds descend to the
compressed fold-factor chain. -/
theorem paper_pom_fold_factor_chain_gap_lsi (D : FoldFactorChainGapLsiData) :
    D.gap_lsi_statement := by
  exact ⟨D.compressedGapLowerBound_proof, D.compressedLsiLowerBound_proof⟩

end Omega.POM
