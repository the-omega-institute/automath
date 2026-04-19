import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The fixed-chart worst-case depth on the height window `|γ| ≤ T` at a prescribed radial defect
`δ`. -/
noncomputable def typedAddressWorstCaseDepth (T δ : ℝ) : ℝ :=
  (4 * δ) / (T ^ 2 + (1 + δ) ^ 2)

/-- The corresponding dyadic bit budget obtained by resolving the worst-case endpoint margin. -/
noncomputable def typedAddressWorstCaseBitBudget (T δ : ℝ) : ℝ :=
  Real.logb 2 ((T ^ 2 + (1 + δ) ^ 2) / (4 * δ))

/-- Paper-facing fixed-chart bit-budget package: the fixed-chart depth law from the first-order
development yields a uniform lower bound on the endpoint margin over `|γ| ≤ T`; requiring dyadic
resolution `2^{-p}` below that margin forces the advertised base-2 logarithmic threshold, and the
budget is sandwiched between two `2 log₂(T)`-scale expressions.
    prop:typed-address-biaxial-completion-comoving-bit-budget -/
theorem paper_typed_address_biaxial_completion_comoving_bit_budget
    {T δ p γ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) (hγ : |γ| ≤ T)
    (hres : (2 : ℝ) ^ (-p) ≤ typedAddressWorstCaseDepth T δ) :
    typedAddressFixedChartDepth δ γ ≥ typedAddressWorstCaseDepth T δ ∧
      typedAddressWorstCaseBitBudget T δ ≤ p ∧
      2 * Real.logb 2 T - Real.logb 2 (4 * δ) ≤ typedAddressWorstCaseBitBudget T δ ∧
      typedAddressWorstCaseBitBudget T δ ≤
        2 * Real.logb 2 (T + (1 + δ)) - Real.logb 2 (4 * δ) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hsq : γ ^ 2 ≤ T ^ 2 := by
    rcases abs_le.mp hγ with ⟨hγl, hγr⟩
    nlinarith
  have hγden_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg γ, hδ]
  have hTden_pos : 0 < T ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg T, hδ]
  have h4δ_pos : 0 < 4 * δ := by
    nlinarith
  have h4δ_ne : 4 * δ ≠ 0 := ne_of_gt h4δ_pos
  have hFirst :=
    paper_typed_address_biaxial_completion_comoving_first_order (δ := δ) (γ := γ) hδ_nonneg
  have hDepthEq :
      typedAddressFixedChartDepth δ γ = (4 * δ) / (γ ^ 2 + (1 + δ) ^ 2) := hFirst.1
  have hDepthLower :
      typedAddressFixedChartDepth δ γ ≥ typedAddressWorstCaseDepth T δ := by
    rw [hDepthEq, typedAddressWorstCaseDepth]
    have hden_le : γ ^ 2 + (1 + δ) ^ 2 ≤ T ^ 2 + (1 + δ) ^ 2 := by
      linarith
    have hdiv :
        (4 * δ) / (T ^ 2 + (1 + δ) ^ 2) ≤ (4 * δ) / (γ ^ 2 + (1 + δ) ^ 2) := by
      exact (div_le_div_iff₀ hTden_pos hγden_pos).2 (by nlinarith)
    linarith
  let budgetArg : ℝ := (T ^ 2 + (1 + δ) ^ 2) / (4 * δ)
  have hbudgetArg_pos : 0 < budgetArg := by
    dsimp [budgetArg]
    positivity
  have hdepth_mul :
      budgetArg * typedAddressWorstCaseDepth T δ = 1 := by
    dsimp [budgetArg, typedAddressWorstCaseDepth]
    field_simp [h4δ_ne, ne_of_gt hTden_pos]
  have hpow_pos : 0 < (2 : ℝ) ^ p := by
    exact Real.rpow_pos_of_pos (by norm_num) p
  have hbudget_le_pow : budgetArg ≤ (2 : ℝ) ^ p := by
    have hmul := mul_le_mul_of_nonneg_right hres hbudgetArg_pos.le
    have hpow_neg : (2 : ℝ) ^ (-p) = ((2 : ℝ) ^ p)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hdiv :
        budgetArg / (2 : ℝ) ^ p ≤ 1 := by
      simpa [div_eq_mul_inv, hpow_neg, mul_assoc, mul_left_comm, mul_comm, hdepth_mul] using hmul
    simpa using (div_le_iff₀ hpow_pos).1 hdiv
  have hbudgetLog :
      typedAddressWorstCaseBitBudget T δ ≤ p := by
    dsimp [typedAddressWorstCaseBitBudget, budgetArg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hbudgetArg_pos hbudget_le_pow
    simpa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using hlog
  have hbudgetArg_lower : T ^ 2 / (4 * δ) ≤ budgetArg := by
    dsimp [budgetArg]
    exact (div_le_div_iff₀ h4δ_pos h4δ_pos).2 (by nlinarith [sq_nonneg (1 + δ)])
  have hbudgetLower :
      2 * Real.logb 2 T - Real.logb 2 (4 * δ) ≤ typedAddressWorstCaseBitBudget T δ := by
    dsimp [typedAddressWorstCaseBitBudget, budgetArg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (show 0 < T ^ 2 / (4 * δ) by positivity) hbudgetArg_lower
    have hleft :
        Real.logb 2 (T ^ 2 / (4 * δ)) = 2 * Real.logb 2 T - Real.logb 2 (4 * δ) := by
      rw [Real.logb_div (show T ^ 2 ≠ 0 by positivity) h4δ_ne, Real.logb_pow]
      norm_num
    simpa [hleft] using hlog
  have hbudgetArg_upper : budgetArg ≤ (T + (1 + δ)) ^ 2 / (4 * δ) := by
    dsimp [budgetArg]
    have hsquare : T ^ 2 + (1 + δ) ^ 2 ≤ (T + (1 + δ)) ^ 2 := by
      nlinarith
    exact (div_le_div_iff₀ h4δ_pos h4δ_pos).2 (by nlinarith [hsquare, h4δ_pos])
  have hbudgetUpper :
      typedAddressWorstCaseBitBudget T δ ≤
        2 * Real.logb 2 (T + (1 + δ)) - Real.logb 2 (4 * δ) := by
    dsimp [typedAddressWorstCaseBitBudget, budgetArg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hbudgetArg_pos hbudgetArg_upper
    have hsum_pos : 0 < T + (1 + δ) := by
      linarith
    have hright :
        Real.logb 2 ((T + (1 + δ)) ^ 2 / (4 * δ)) =
          2 * Real.logb 2 (T + (1 + δ)) - Real.logb 2 (4 * δ) := by
      rw [Real.logb_div (show (T + (1 + δ)) ^ 2 ≠ 0 by positivity) h4δ_ne, Real.logb_pow]
      norm_num
    simpa [hright] using hlog
  exact ⟨hDepthLower, hbudgetLog, hbudgetLower, hbudgetUpper⟩

end Omega.TypedAddressBiaxialCompletion
