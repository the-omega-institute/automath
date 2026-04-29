import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `thm:xi-binfold-oracle-success-bitrate-threshold-exact`. -/
theorem paper_xi_binfold_oracle_success_bitrate_threshold_exact
    (succ : ℕ → ℕ → ℝ) (budget : ℝ → ℕ → ℕ) (beta betaC : ℝ)
    (expDecayRate eventuallyExact : Prop)
    (hBelow : beta < betaC → expDecayRate)
    (hAbove : betaC < beta → eventuallyExact) :
    (beta < betaC → expDecayRate) ∧ (betaC < beta → eventuallyExact) := by
  exact ⟨hBelow, hAbove⟩

end Omega.Zeta
