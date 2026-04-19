import Mathlib.Tactic
import Omega.GU.Window6BinfoldLastbitLecamEquivalence

namespace Omega.GU

/-- Data package for the window-`6` bin-fold KL limit constant. It extends the last-bit Le Cam
comparison data by adding a continuity estimate from total variation to the KL observable and the
closed form of the Bernoulli pushforward limit constant. -/
structure Window6BinfoldKLLimitData extends Window6BinfoldLastbitLeCamData where
  klMu : ℝ
  klBernoulli : ℝ
  limitConstant : ℝ
  entropyContinuity :
    abs (klMu - klBernoulli) <= abs (tvMuUniform - tvLastbitUniform)
  hBernoulliClosedForm : klBernoulli = limitConstant

/-- The Bernoulli pushforward already attains the closed-form limit constant. -/
def Window6BinfoldKLLimitData.bernoulliClosedForm (d : Window6BinfoldKLLimitData) : Prop :=
  d.klBernoulli = d.limitConstant

/-- Existence of a KL limit constant with the expected exponential error term. -/
def Window6BinfoldKLLimitData.limitExists (d : Window6BinfoldKLLimitData) : Prop :=
  ∃ L, abs (d.klMu - L) <= 2 * d.C * (d.phi / 2) ^ d.m

/-- The transported KL estimate against the Bernoulli closed-form constant. -/
def Window6BinfoldKLLimitData.errorBound (d : Window6BinfoldKLLimitData) : Prop :=
  abs (d.klMu - d.limitConstant) <= 2 * d.C * (d.phi / 2) ^ d.m

/-- The last-bit Le Cam estimate upgrades the Bernoulli KL closed form to a KL limit constant, and
the continuity estimate transports the same exponential rate to the KL observable.
    cor:window6-binfold-kl-limit-constant -/
theorem paper_window6_binfold_kl_limit_constant (d : Window6BinfoldKLLimitData) :
    d.limitExists ∧ d.bernoulliClosedForm ∧ d.errorBound := by
  have hLastbit :
      abs (d.tvMuUniform - d.tvLastbitUniform) <= 2 * d.C * (d.phi / 2) ^ d.m := by
    exact
      (paper_window6_binfold_lastbit_lecam_equivalence d.toWindow6BinfoldLastbitLeCamData).2
  have hError : d.errorBound := by
    dsimp [Window6BinfoldKLLimitData.errorBound]
    calc
      abs (d.klMu - d.limitConstant) = abs (d.klMu - d.klBernoulli) := by
        rw [d.hBernoulliClosedForm]
      _ <= abs (d.tvMuUniform - d.tvLastbitUniform) := d.entropyContinuity
      _ <= 2 * d.C * (d.phi / 2) ^ d.m := hLastbit
  refine ⟨?_, ?_, hError⟩
  refine ⟨d.limitConstant, ?_⟩
  simpa [Window6BinfoldKLLimitData.errorBound] using hError
  simpa [Window6BinfoldKLLimitData.bernoulliClosedForm] using d.hBernoulliClosedForm

end Omega.GU
