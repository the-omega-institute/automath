import Mathlib.Tactic
import Omega.Folding.BernoulliPBitpairLaw
import Omega.Folding.BernoulliPPressureQuartic

namespace Omega.Folding

/-- Closed form of the Bernoulli-`p` output density `q(p) = P(Y_t = 1)`. -/
def bernoulliPOutputDensityClosedForm (p : ℚ) : ℚ :=
  p * (p ^ 3 - p + 1) / (1 + p ^ 3)

/-- Closed form of the Bernoulli-`p` mismatch density `γ(p) = P(X_t ≠ Y_t)`. -/
def bernoulliPMismatchDensityClosedForm (p : ℚ) : ℚ :=
  p ^ 2 * (3 - 2 * p) / (1 + p ^ 3)

/-- The elimination quartic satisfied by the pair `(q(p), γ(p))`. -/
def bernoulliPOutputMismatchEliminationQuartic (q γ : ℚ) : ℚ :=
  γ ^ 4 + 9 * γ ^ 3 * q + 4 * γ ^ 3 +
    27 * γ ^ 2 * q ^ 2 + 18 * γ ^ 2 * q - 23 * γ ^ 2 +
    35 * γ * q ^ 3 + 72 * γ * q ^ 2 - 54 * γ * q + 23 * γ +
    70 * q ^ 3 - 69 * q ^ 2

/-- The explicit Bernoulli-`p` closed forms satisfy the output/mismatch state equation, and
substituting them into the eliminated quartic relation gives zero.
    thm:fold-bernoulli-p-output-mismatch-elimination-curve -/
theorem paper_fold_bernoulli_p_output_mismatch_elimination_curve
    (p : ℚ) (hDen : 1 + p ^ 3 ≠ 0) :
    bernoulliPMismatchDensityClosedForm p =
      (3 - 2 * p) * (p - bernoulliPOutputDensityClosedForm p) ∧
    bernoulliPOutputMismatchEliminationQuartic
        (bernoulliPOutputDensityClosedForm p) (bernoulliPMismatchDensityClosedForm p) = 0 := by
  refine ⟨?_, ?_⟩
  · unfold bernoulliPMismatchDensityClosedForm bernoulliPOutputDensityClosedForm
    field_simp [hDen]
    ring
  · unfold bernoulliPOutputMismatchEliminationQuartic
      bernoulliPMismatchDensityClosedForm bernoulliPOutputDensityClosedForm
    field_simp [hDen]
    ring

end Omega.Folding
