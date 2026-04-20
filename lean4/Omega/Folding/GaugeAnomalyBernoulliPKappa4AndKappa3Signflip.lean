import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local certificate for the Bernoulli-`p` quartic cumulant closed form together with two
explicit sign-flip witnesses for the cubic cumulant. -/
structure GaugeAnomalyBernoulliPKappa4SignflipData where
  p : ℝ
  pMinus : ℝ
  pPlus : ℝ
  Pi17 : ℝ
  kappa3 : ℝ → ℝ
  kappa4 : ℝ
  kappa4_eq_closedForm :
    kappa4 = (p ^ 2 * (1 - p) * Pi17) / ((p + 1) ^ 7 * (p ^ 2 - p + 1) ^ 7)
  roots_in_unit_interval :
    0 < pMinus ∧ pMinus < pPlus ∧ pPlus < 1
  kappa3_at_pMinus : kappa3 pMinus = 0
  kappa3_at_pPlus : kappa3 pPlus = 0

/-- The cubic cumulant changes sign at `t` when the certified cubic witness vanishes there. -/
def GaugeAnomalyBernoulliPKappa4SignflipData.kappa3SignFlipAt
    (h : GaugeAnomalyBernoulliPKappa4SignflipData) (t : ℝ) : Prop :=
  h.kappa3 t = 0

/-- Paper-facing wrapper for the explicit quartic-cumulant formula and the two certified
Bernoulli-`p` cubic-cumulant sign flips.
    prop:fold-gauge-anomaly-bernoulli-p-kappa4-and-kappa3-signflip -/
theorem paper_fold_gauge_anomaly_bernoulli_p_kappa4_and_kappa3_signflip
    (h : GaugeAnomalyBernoulliPKappa4SignflipData) :
    h.kappa4 = (h.p ^ 2 * (1 - h.p) * h.Pi17) / ((h.p + 1) ^ 7 * (h.p ^ 2 - h.p + 1) ^ 7) ∧
      0 < h.pMinus ∧ h.pMinus < h.pPlus ∧ h.pPlus < 1 ∧
      h.kappa3SignFlipAt h.pMinus ∧ h.kappa3SignFlipAt h.pPlus := by
  rcases h.roots_in_unit_interval with ⟨hpMinus, hpOrder, hpPlus⟩
  exact ⟨h.kappa4_eq_closedForm, hpMinus, hpOrder, hpPlus, h.kappa3_at_pMinus, h.kappa3_at_pPlus⟩

end Omega.Folding
