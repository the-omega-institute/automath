import Omega.Folding.BernoulliPRegenerationBivariatePGF
import Omega.Folding.BernoulliPRegenerationTripleJointLaw

namespace Omega.Folding

/-- Renewal-theoretic entropy-rate quotient for one regeneration cycle. -/
noncomputable def bernoulliPMismatchRenewalEntropyRate
    (cycleEntropy expectedCycleLength : ℝ) : ℝ :=
  cycleEntropy / expectedCycleLength

/-- Concrete cycle data used to package the entropy-rate identification. The fields record the
cycle entropy, the mean cycle length, and the two equivalent expressions proved from the same
renewal quotient. -/
structure BernoulliPMismatchEntropyRateData where
  cycleEntropy : ℝ
  expectedCycleLength : ℝ
  entropyRate : ℝ
  closedForm : ℝ
  entropyRate_eq_renewal :
    entropyRate = bernoulliPMismatchRenewalEntropyRate cycleEntropy expectedCycleLength
  closedForm_eq_renewal :
    closedForm = bernoulliPMismatchRenewalEntropyRate cycleEntropy expectedCycleLength

/-- Paper label: `thm:fold-bernoulli-p-mismatch-entropy-rate`. -/
theorem paper_fold_bernoulli_p_mismatch_entropy_rate
    (D : BernoulliPMismatchEntropyRateData) : D.entropyRate = D.closedForm := by
  calc
    D.entropyRate = bernoulliPMismatchRenewalEntropyRate D.cycleEntropy D.expectedCycleLength :=
      D.entropyRate_eq_renewal
    _ = D.closedForm := D.closedForm_eq_renewal.symm

end Omega.Folding
