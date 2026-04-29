import Omega.Zeta.XiFoldbinTwoPhaseFreeEnergyVariational
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The golden-ratio parameter used by the bin-fold one-constant package. -/
def xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi : ℝ :=
  xi_foldbin_two_phase_free_energy_variational_phi

/-- The square-root normalization used by the bin-fold one-constant package. -/
def xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_sqrt5 : ℝ :=
  xi_foldbin_two_phase_free_energy_variational_sqrt5

/-- The hidden-bit constant shared by the finite-layer entropy identities. -/
def xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant : ℝ :=
  Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi /
    (xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi *
      xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_sqrt5)

/-- The stable-cardinality intercept before subtracting the hidden-bit constant. -/
def xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_uniformIntercept : ℝ :=
  2 * Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi -
    Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_sqrt5

/-- Concrete finite-layer data for the hidden budget, visible entropy, and uniform-baseline KL. -/
structure xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_data where
  m : ℕ
  hiddenBudget : ℝ
  visibleEntropy : ℝ
  uniformLogCardinality : ℝ
  uniformBaselineKl : ℝ
  hiddenError : ℝ
  cardinalityError : ℝ
  limitingConstant : ℝ
  hiddenBudgetExpansion :
    hiddenBudget =
      (m : ℝ) *
          Real.log (2 / xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi) -
        xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant +
          hiddenError
  entropyIdentity : visibleEntropy = (m : ℝ) * Real.log 2 - hiddenBudget
  uniformLogCardinalityExpansion :
    uniformLogCardinality =
      (m : ℝ) * Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi +
        xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_uniformIntercept +
          cardinalityError
  uniformBaselineKlIdentity : uniformBaselineKl = uniformLogCardinality - visibleEntropy
  limitingConstant_eq :
    limitingConstant =
      xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_uniformIntercept -
        xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant

/-- Paper-facing finite algebra statement for the bin-fold one-constant package. -/
def xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_statement
    (D : xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_data) : Prop :=
  D.hiddenBudget =
      (D.m : ℝ) *
          Real.log (2 / xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi) -
        xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant +
          D.hiddenError ∧
    D.visibleEntropy =
      (D.m : ℝ) * Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi +
        xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant -
          D.hiddenError ∧
      D.uniformBaselineKl =
        D.limitingConstant + D.cardinalityError + D.hiddenError ∧
        D.limitingConstant =
          2 * Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi -
            Real.log xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_sqrt5 -
              xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_hiddenConstant

/-- Paper label: `thm:xi-foldbin-hidden-budget-visible-entropy-kl-one-constant`. -/
theorem paper_xi_foldbin_hidden_budget_visible_entropy_kl_one_constant
    (D : xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_data) :
    xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_statement D := by
  have htwo := paper_xi_foldbin_two_phase_free_energy_variational
  have hphi_pos :
      0 < xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi := by
    simpa [xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi] using htwo.1
  have hphi_ne :
      xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_phi ≠ 0 := hphi_pos.ne'
  refine ⟨D.hiddenBudgetExpansion, ?_, ?_, ?_⟩
  · rw [D.entropyIdentity, D.hiddenBudgetExpansion]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hphi_ne]
    ring
  · rw [D.uniformBaselineKlIdentity, D.uniformLogCardinalityExpansion, D.entropyIdentity,
      D.hiddenBudgetExpansion, D.limitingConstant_eq]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hphi_ne]
    ring
  · rw [D.limitingConstant_eq,
      xi_foldbin_hidden_budget_visible_entropy_kl_one_constant_uniformIntercept]

end

end Omega.Zeta
