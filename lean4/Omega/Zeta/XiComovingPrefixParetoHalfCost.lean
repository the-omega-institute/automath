import Omega.Zeta.XiComovingPrefixEndpointBarrierLaw

namespace Omega.Zeta

/-- Same-weight total cost: prefix depth plus the endpoint budget. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_total
    (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  (B : ℝ) + xiComovingPrefixPmin T δ₀ B

/-- Closed total-cost form after substituting the dyadic prefix error scale. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_closed
    (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  (B : ℝ) +
    Real.log
        ((((T * (2 : ℝ) ^ (-(B : ℝ))) ^ (2 : ℕ)) + (1 + δ₀) ^ (2 : ℕ)) /
          (4 * δ₀)) /
      Real.log 2

/-- Prefix-dominated budget branch. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_prefix_budget
    (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  Real.log (((xiComovingPrefixError T B) ^ (2 : ℕ)) / (4 * δ₀)) / Real.log 2

/-- Prefix-dominated total-cost branch. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_prefix_total
    (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  (B : ℝ) + xi_comoving_prefix_pareto_half_cost_prefix_budget T δ₀ B

/-- One-bit upper envelope for the prefix-dominated branch. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_prefix_total_upper
    (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  (B : ℝ) +
    Real.log ((2 * (xiComovingPrefixError T B) ^ (2 : ℕ)) / (4 * δ₀)) /
      Real.log 2

/-- Saturated endpoint-budget branch. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_saturated_budget (δ₀ : ℝ) : ℝ :=
  Real.log (((1 + δ₀) ^ (2 : ℕ)) / (4 * δ₀)) / Real.log 2

/-- One-bit upper envelope for the saturated endpoint-budget branch. -/
noncomputable def xi_comoving_prefix_pareto_half_cost_saturated_budget_upper (δ₀ : ℝ) : ℝ :=
  Real.log ((2 * (1 + δ₀) ^ (2 : ℕ)) / (4 * δ₀)) / Real.log 2

lemma xi_comoving_prefix_pareto_half_cost_log_div_le_log_div
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd : 0 < d) :
    Real.log (a / d) / Real.log 2 ≤ Real.log (b / d) / Real.log 2 := by
  have hratio_pos : 0 < a / d := div_pos ha hd
  have hratio_le : a / d ≤ b / d := div_le_div_of_nonneg_right hab hd.le
  have hlog_le : Real.log (a / d) ≤ Real.log (b / d) :=
    Real.log_le_log hratio_pos hratio_le
  exact div_le_div_of_nonneg_right hlog_le (Real.log_pos one_lt_two).le

/-- Exact Pareto half-cost package: the endpoint law gives the total-cost closed form; if the
prefix error dominates the endpoint floor, the total cost lies between the prefix branch and its
one-bit envelope, while in the saturated regime the endpoint budget lies between the saturated
branch and its one-bit envelope. -/
def xi_comoving_prefix_pareto_half_cost_statement : Prop :=
  ∀ {T δ₀ : ℝ} {B : ℕ}, 0 < δ₀ → δ₀ ≤ 1 / 2 →
    xi_comoving_prefix_pareto_half_cost_total T δ₀ B =
        xi_comoving_prefix_pareto_half_cost_closed T δ₀ B ∧
      ((1 + δ₀) ^ (2 : ℕ) ≤ (xiComovingPrefixError T B) ^ (2 : ℕ) →
        xi_comoving_prefix_pareto_half_cost_prefix_total T δ₀ B ≤
            xi_comoving_prefix_pareto_half_cost_total T δ₀ B ∧
          xi_comoving_prefix_pareto_half_cost_total T δ₀ B ≤
            xi_comoving_prefix_pareto_half_cost_prefix_total_upper T δ₀ B) ∧
      ((xiComovingPrefixError T B) ^ (2 : ℕ) ≤ (1 + δ₀) ^ (2 : ℕ) →
        xi_comoving_prefix_pareto_half_cost_saturated_budget δ₀ ≤ xiComovingPrefixPmin T δ₀ B ∧
          xiComovingPrefixPmin T δ₀ B ≤
            xi_comoving_prefix_pareto_half_cost_saturated_budget_upper δ₀)

/-- Paper label: `cor:xi-comoving-prefix-pareto-half-cost`. -/
theorem paper_xi_comoving_prefix_pareto_half_cost :
    xi_comoving_prefix_pareto_half_cost_statement := by
  intro T δ₀ B hδ₀ hδ₀_half
  have hbarrier :=
    paper_xi_comoving_prefix_endpoint_barrier_law (T := T) (δ₀ := δ₀) (B := B)
      hδ₀ hδ₀_half
  have hbudget :
      xiComovingPrefixPmin T δ₀ B =
        Real.log
            ((((xiComovingPrefixError T B) ^ (2 : ℕ)) + (1 + δ₀) ^ (2 : ℕ)) /
              (4 * δ₀)) /
          Real.log 2 := hbarrier.2
  have hclosed :
      xi_comoving_prefix_pareto_half_cost_total T δ₀ B =
        xi_comoving_prefix_pareto_half_cost_closed T δ₀ B := by
    simpa [xi_comoving_prefix_pareto_half_cost_total,
      xi_comoving_prefix_pareto_half_cost_closed, xiComovingPrefixError] using
      congrArg (fun x => (B : ℝ) + x) hbudget
  refine ⟨hclosed, ?_, ?_⟩
  · intro hdominates
    have hden : 0 < 4 * δ₀ := by positivity
    have hfloor_pos : 0 < (1 + δ₀) ^ (2 : ℕ) := by positivity
    have herror_pos : 0 < (xiComovingPrefixError T B) ^ (2 : ℕ) :=
      lt_of_lt_of_le hfloor_pos hdominates
    constructor
    · have hmono :
          xi_comoving_prefix_pareto_half_cost_prefix_budget T δ₀ B ≤
            xiComovingPrefixPmin T δ₀ B := by
        have hstep :
            (xiComovingPrefixError T B) ^ (2 : ℕ) ≤
              (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (1 + δ₀)]
        calc
          xi_comoving_prefix_pareto_half_cost_prefix_budget T δ₀ B
              ≤
                Real.log
                    ((((xiComovingPrefixError T B) ^ (2 : ℕ)) +
                        (1 + δ₀) ^ (2 : ℕ)) /
                      (4 * δ₀)) /
                  Real.log 2 := by
                simpa [xi_comoving_prefix_pareto_half_cost_prefix_budget] using
                  xi_comoving_prefix_pareto_half_cost_log_div_le_log_div
                    herror_pos hstep hden
          _ = xiComovingPrefixPmin T δ₀ B := hbudget.symm
      simpa [xi_comoving_prefix_pareto_half_cost_prefix_total,
        xi_comoving_prefix_pareto_half_cost_total] using
        add_le_add_left hmono (B : ℝ)
    · have hmono :
          xiComovingPrefixPmin T δ₀ B ≤
            Real.log ((2 * (xiComovingPrefixError T B) ^ (2 : ℕ)) / (4 * δ₀)) /
              Real.log 2 := by
        have hsum_le :
            (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) ≤
              2 * (xiComovingPrefixError T B) ^ (2 : ℕ) := by
          nlinarith
        have hsum_pos :
            0 <
              (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) := by
          nlinarith
        calc
          xiComovingPrefixPmin T δ₀ B
              =
                Real.log
                    ((((xiComovingPrefixError T B) ^ (2 : ℕ)) +
                        (1 + δ₀) ^ (2 : ℕ)) /
                      (4 * δ₀)) /
                  Real.log 2 := hbudget
          _ ≤ Real.log ((2 * (xiComovingPrefixError T B) ^ (2 : ℕ)) / (4 * δ₀)) /
              Real.log 2 :=
                xi_comoving_prefix_pareto_half_cost_log_div_le_log_div hsum_pos hsum_le hden
      simpa [xi_comoving_prefix_pareto_half_cost_total,
        xi_comoving_prefix_pareto_half_cost_prefix_total_upper] using
        add_le_add_left hmono (B : ℝ)
  · intro hsaturated
    have hden : 0 < 4 * δ₀ := by positivity
    have hfloor_pos : 0 < (1 + δ₀) ^ (2 : ℕ) := by positivity
    constructor
    · have hstep :
        (1 + δ₀) ^ (2 : ℕ) ≤
          (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (xiComovingPrefixError T B)]
      calc
        xi_comoving_prefix_pareto_half_cost_saturated_budget δ₀
            ≤
              Real.log
                  ((((xiComovingPrefixError T B) ^ (2 : ℕ)) + (1 + δ₀) ^ (2 : ℕ)) /
                    (4 * δ₀)) /
                Real.log 2 := by
              simpa [xi_comoving_prefix_pareto_half_cost_saturated_budget] using
                xi_comoving_prefix_pareto_half_cost_log_div_le_log_div hfloor_pos hstep hden
        _ = xiComovingPrefixPmin T δ₀ B := hbudget.symm
    · have hsum_le :
          (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) ≤
            2 * (1 + δ₀) ^ (2 : ℕ) := by
        nlinarith
      have hsum_pos :
          0 < (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) := by
        nlinarith
      calc
        xiComovingPrefixPmin T δ₀ B
            =
              Real.log
                  ((((xiComovingPrefixError T B) ^ (2 : ℕ)) + (1 + δ₀) ^ (2 : ℕ)) /
                    (4 * δ₀)) /
                Real.log 2 := hbudget
        _ ≤ xi_comoving_prefix_pareto_half_cost_saturated_budget_upper δ₀ := by
          simpa [xi_comoving_prefix_pareto_half_cost_saturated_budget_upper] using
            xi_comoving_prefix_pareto_half_cost_log_div_le_log_div hsum_pos hsum_le hden

end Omega.Zeta
