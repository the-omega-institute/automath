import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Total variation distance for finite real-valued laws, normalized as half the `L¹` distance. -/
noncomputable def
    conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_totalVariation
    {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ ω : Ω, |p ω - q ω|

/-- Risk of a finite decision rule after the loss has been averaged over its action kernel. -/
noncomputable def
    conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (conditionalRisk : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p ω * conditionalRisk ω

private lemma conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_abs_sum_bound
    {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ) (conditionalRisk : Ω → ℝ)
    (Lnorm : ℝ) (hBound : ∀ ω, |conditionalRisk ω| ≤ Lnorm) :
    |∑ ω : Ω, (p ω - q ω) * conditionalRisk ω| ≤
      Lnorm * ∑ ω : Ω, |p ω - q ω| := by
  calc
    |∑ ω : Ω, (p ω - q ω) * conditionalRisk ω|
        ≤ ∑ ω : Ω, |(p ω - q ω) * conditionalRisk ω| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω : Ω, |p ω - q ω| * |conditionalRisk ω| := by
        simp [abs_mul, mul_comm]
    _ ≤ ∑ ω : Ω, |p ω - q ω| * Lnorm := by
        exact Finset.sum_le_sum fun ω _hω =>
          mul_le_mul_of_nonneg_left (hBound ω) (abs_nonneg (p ω - q ω))
    _ = Lnorm * ∑ ω : Ω, |p ω - q ω| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro ω _hω
        ring

private lemma conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_tv_risk_bound
    {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ) (conditionalRisk : Ω → ℝ)
    (Lnorm eps : ℝ) (hLnorm : 0 ≤ Lnorm) (hBound : ∀ ω, |conditionalRisk ω| ≤ Lnorm)
    (hTV :
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_totalVariation p q ≤ eps) :
    |conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk p
        conditionalRisk -
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk q
        conditionalRisk| ≤
      2 * Lnorm * eps := by
  have hdiff :
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk p
          conditionalRisk -
        conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk q
          conditionalRisk =
        ∑ ω : Ω, (p ω - q ω) * conditionalRisk ω := by
    unfold conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ω _hω
    ring
  have hsum_nonneg : 0 ≤ ∑ ω : Ω, |p ω - q ω| := Finset.sum_nonneg fun ω _hω => abs_nonneg _
  have hsum_le : ∑ ω : Ω, |p ω - q ω| ≤ 2 * eps := by
    unfold conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_totalVariation at hTV
    nlinarith
  calc
    |conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk p
        conditionalRisk -
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk q
        conditionalRisk|
        = |∑ ω : Ω, (p ω - q ω) * conditionalRisk ω| := by rw [hdiff]
    _ ≤ Lnorm * ∑ ω : Ω, |p ω - q ω| :=
        conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_abs_sum_bound
          p q conditionalRisk Lnorm hBound
    _ ≤ Lnorm * (2 * eps) := by
        exact mul_le_mul_of_nonneg_left hsum_le hLnorm
    _ = 2 * Lnorm * eps := by ring

/-- Paper label:
`thm:conclusion-binfold-escort-fixed-n-bounded-loss-decision-collapse`. A finite Markov-kernel
collapse within total-variation error `C_{n,Q} (φ / 2)^m` changes every bounded-loss risk by at
most `2 ||L||` times that error. -/
theorem paper_conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse
    {Ω : Type*} [Fintype Ω] (fullLaw collapsedLaw : Ω → ℝ)
    (conditionalRisk : Ω → ℝ) (Lnorm CnQ : ℝ) (m : ℕ)
    (hLnorm : 0 ≤ Lnorm) (hBound : ∀ ω, |conditionalRisk ω| ≤ Lnorm)
    (hCollapse :
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_totalVariation
          fullLaw collapsedLaw ≤ CnQ * (Real.goldenRatio / 2) ^ m) :
    |conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk fullLaw
        conditionalRisk -
      conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_linearRisk collapsedLaw
        conditionalRisk| ≤
      2 * Lnorm * (CnQ * (Real.goldenRatio / 2) ^ m) := by
  exact conclusion_binfold_escort_fixed_n_bounded_loss_decision_collapse_tv_risk_bound
    fullLaw collapsedLaw conditionalRisk Lnorm (CnQ * (Real.goldenRatio / 2) ^ m)
    hLnorm hBound hCollapse

end Omega.Conclusion
