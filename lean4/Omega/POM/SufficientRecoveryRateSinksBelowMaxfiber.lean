import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.POM.MesoscopicReversibleWindowStrictGap

namespace Omega.POM

open Filter

noncomputable section

/-- Concrete data for the linear-budget specialization of the mesoscopic strict-gap estimate. The
sequence `successAlongBudget m` stands for `Succ_m(B_m)` along the budget `B_m = ⌊β m⌋`. -/
structure pom_sufficient_recovery_rate_sinks_below_maxfiber_data where
  beta : ℝ
  alphaStar : ℝ
  alphaStar2 : ℝ
  gStar : ℝ
  successAlongBudget : ℕ → ℝ
  gap_below_log2 : alphaStar + gStar < Real.log 2
  beta_lower : alphaStar2 / Real.log 2 < beta
  beta_upper : beta < alphaStar / Real.log 2
  success_formula :
    ∀ m : ℕ,
      successAlongBudget m =
        1 - Real.exp (-(Real.log 2 - alphaStar - gStar) * (m : ℝ))

/-- The linear budget sequence `B_m = ⌊β m⌋`. -/
noncomputable def pom_sufficient_recovery_rate_sinks_below_maxfiber_budget
    (D : pom_sufficient_recovery_rate_sinks_below_maxfiber_data) (m : ℕ) : Int :=
  Int.floor (D.beta * (m : ℝ))

/-- The strict negative exponent controlling the failure probability. -/
noncomputable def pom_sufficient_recovery_rate_sinks_below_maxfiber_gap
    (D : pom_sufficient_recovery_rate_sinks_below_maxfiber_data) : ℝ :=
  Real.log 2 - D.alphaStar - D.gStar

/-- Paper-facing success statement for the linear-budget specialization. -/
def pom_sufficient_recovery_rate_sinks_below_maxfiber_holds
    (D : pom_sufficient_recovery_rate_sinks_below_maxfiber_data) : Prop :=
  (∀ m : ℕ,
      pom_sufficient_recovery_rate_sinks_below_maxfiber_budget D m =
        Int.floor (D.beta * (m : ℝ))) ∧
    Tendsto D.successAlongBudget atTop (nhds 1)

/-- Paper label: `cor:pom-sufficient-recovery-rate-sinks-below-maxfiber`. Specializing the
strict-gap theorem to `B_m = ⌊β m⌋` records the exact budget identity and the exponential success
formula. Because `alphaStar + gStar < log 2`, the failure exponent is negative, so the success
probability tends to `1`. -/
theorem paper_pom_sufficient_recovery_rate_sinks_below_maxfiber
    (D : pom_sufficient_recovery_rate_sinks_below_maxfiber_data) :
    pom_sufficient_recovery_rate_sinks_below_maxfiber_holds D := by
  let paper_pom_sufficient_recovery_rate_sinks_below_maxfiber_exactWindowFormula : Prop :=
    ∀ m : ℕ,
      pom_sufficient_recovery_rate_sinks_below_maxfiber_budget D m =
        Int.floor (D.beta * (m : ℝ))
  let paper_pom_sufficient_recovery_rate_sinks_below_maxfiber_successAsymptotic : Prop :=
    ∀ m : ℕ,
      D.successAlongBudget m =
        1 - Real.exp (-(pom_sufficient_recovery_rate_sinks_below_maxfiber_gap D) * (m : ℝ))
  have hStrictGap :=
    paper_pom_mesoscopic_reversible_window_strict_gap
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      D.alphaStar D.gStar D.alphaStar2
      paper_pom_sufficient_recovery_rate_sinks_below_maxfiber_exactWindowFormula
      paper_pom_sufficient_recovery_rate_sinks_below_maxfiber_successAsymptotic
      (by
        intro m
        rfl)
      (by
        intro m
        simpa [paper_pom_sufficient_recovery_rate_sinks_below_maxfiber_successAsymptotic,
          pom_sufficient_recovery_rate_sinks_below_maxfiber_gap] using D.success_formula m)
  have hgap_pos : 0 < pom_sufficient_recovery_rate_sinks_below_maxfiber_gap D := by
    dsimp [pom_sufficient_recovery_rate_sinks_below_maxfiber_gap]
    linarith [D.gap_below_log2]
  have hExp :
      Tendsto
        (fun m : ℕ =>
          Real.exp (-(pom_sufficient_recovery_rate_sinks_below_maxfiber_gap D) * (m : ℝ)))
        atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    simpa [neg_mul] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap_pos))
  have hMain :
      Tendsto
        (fun m : ℕ =>
          1 - Real.exp (-(pom_sufficient_recovery_rate_sinks_below_maxfiber_gap D) * (m : ℝ)))
        atTop (nhds 1) := by
    have :
        Tendsto
          (fun m : ℕ =>
            (1 : ℝ) - Real.exp (-(pom_sufficient_recovery_rate_sinks_below_maxfiber_gap D) *
              (m : ℝ)))
          atTop (nhds ((1 : ℝ) - 0)) :=
      Tendsto.sub tendsto_const_nhds hExp
    simpa using this
  refine ⟨hStrictGap.1, ?_⟩
  refine Tendsto.congr' ?_ hMain
  exact Eventually.of_forall fun m => (hStrictGap.2 m).symm

end

end Omega.POM
