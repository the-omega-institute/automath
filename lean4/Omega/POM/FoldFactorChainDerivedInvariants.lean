import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The fold-factor-chain spectral-gap lower bound `2 / m` from the paper. -/
noncomputable def foldFactorChainGapLower (m : ℕ) : ℝ :=
  2 / (m : ℝ)

/-- The corresponding conductance lower bound `1 / m`. -/
noncomputable def foldFactorChainConductanceLower (m : ℕ) : ℝ :=
  1 / (m : ℝ)

/-- The logarithmic Sobolev lower bound `1 / m`. -/
noncomputable def foldFactorChainLogSobolevLower (m : ℕ) : ℝ :=
  1 / (m : ℝ)

/-- Gross hypercontractive exponent `q(t) = 1 + exp(2 t / m)`. -/
noncomputable def foldFactorChainHypercontractiveExponent (m : ℕ) (t : ℝ) : ℝ :=
  1 + Real.exp (2 * t / (m : ℝ))

/-- Herbst-Chernoff tail profile `2 exp(-t^2 / (2m))`. -/
noncomputable def foldFactorChainSubgaussianTail (m : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (-(t ^ 2) / (2 * (m : ℝ)))

/-- Paper-facing package of the fold-factor-chain derived invariants: the conductance lower bound
is the Cheeger half-gap, the continuous-time hypercontractive exponent normalizes to `2` at
`t = 0` and stays above `1`, and the Herbst-Chernoff profile is positive and at most `2`.
    cor:pom-fold-factor-chain-derived-invariants -/
theorem paper_pom_fold_factor_chain_derived_invariants (m : ℕ) (hm : 1 ≤ m) :
    foldFactorChainConductanceLower m = foldFactorChainGapLower m / 2 ∧
      foldFactorChainLogSobolevLower m = 1 / (m : ℝ) ∧
      foldFactorChainHypercontractiveExponent m 0 = 2 ∧
      (∀ t : ℝ, 0 ≤ t → 1 < foldFactorChainHypercontractiveExponent m t) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < foldFactorChainSubgaussianTail m t ∧ foldFactorChainSubgaussianTail m t ≤ 2) := by
  have hm_nat : 0 < m := by omega
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm_nat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold foldFactorChainConductanceLower foldFactorChainGapLower
    field_simp [hm_real.ne']
  · rfl
  · norm_num [foldFactorChainHypercontractiveExponent]
  · intro t ht
    let _ := ht
    unfold foldFactorChainHypercontractiveExponent
    have hexp_pos : 0 < Real.exp (2 * t / (m : ℝ)) := Real.exp_pos _
    linarith
  · intro t ht
    unfold foldFactorChainSubgaussianTail
    have hexp_pos : 0 < Real.exp (-(t ^ 2) / (2 * (m : ℝ))) := Real.exp_pos _
    have hexp_le : Real.exp (-(t ^ 2) / (2 * (m : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have hnum_nonpos : -(t ^ 2) ≤ 0 := by nlinarith [sq_nonneg t]
      have hden_nonneg : 0 ≤ 2 * (m : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    constructor
    · positivity
    · nlinarith

end Omega.POM
