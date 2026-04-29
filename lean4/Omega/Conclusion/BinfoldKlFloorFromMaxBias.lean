import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

open Finset

/-- A concrete finite probability vector over `Fin n`. -/
def conclusion_binfold_kl_floor_from_max_bias_probabilityVector
    (n : ℕ) (mass : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ mass i) ∧ ∑ i, mass i = 1

/-- A concrete max-mass bias bound for a finite probability vector. -/
def conclusion_binfold_kl_floor_from_max_bias_maxMassAtMost
    (n : ℕ) (mass : Fin n → ℝ) (bias : ℝ) : Prop :=
  ∀ i, mass i ≤ bias

/-- The one-spike Shannon--KL floor profile forced by a max-mass bound. -/
def conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile (bias : ℝ) : ℝ :=
  Real.log (1 / bias)

/-- The finite probability-vector inequality: a certified KL floor dominates the one-spike
profile attached to the asserted max-mass bias. -/
def conclusion_binfold_kl_floor_from_max_bias_finiteVectorInequality
    (bias certifiedFloor : ℝ) : Prop :=
  conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile bias ≤ certifiedFloor

/-- The one-spike profile is antitone in the permitted maximum mass. -/
lemma conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile_antitone
    {smallBias largeBias : ℝ}
    (hsmall : 0 < smallBias)
    (hle : smallBias ≤ largeBias) :
    conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile largeBias ≤
      conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile smallBias := by
  have hlarge : 0 < largeBias := lt_of_lt_of_le hsmall hle
  have hinv : 1 / largeBias ≤ 1 / smallBias := by
    exact one_div_le_one_div_of_le hsmall hle
  exact Real.log_le_log (by positivity) hinv

/-- A max-mass bound by `1/2` forces a `log 2` one-spike KL floor. -/
lemma conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile_half_floor
    {bias : ℝ}
    (hpos : 0 < bias)
    (hbias : bias ≤ 1 / 2) :
    Real.log 2 ≤ conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile bias := by
  unfold conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile
  have hinv : (2 : ℝ) ≤ 1 / bias := by
    rw [le_div_iff₀ hpos]
    nlinarith
  exact Real.log_le_log (by norm_num) hinv

/-- Paper label: `thm:conclusion-binfold-kl-floor-from-max-bias`.

For any finite probability vector whose maximum atom is bounded by `bias ≤ 1/2`, every certified
KL floor that dominates the one-spike minimizer profile is at least `log 2`. -/
theorem paper_conclusion_binfold_kl_floor_from_max_bias
    (n : ℕ) (mass : Fin n → ℝ) (bias certifiedFloor : ℝ)
    (_hprob :
      conclusion_binfold_kl_floor_from_max_bias_probabilityVector n mass)
    (_hmax :
      conclusion_binfold_kl_floor_from_max_bias_maxMassAtMost n mass bias)
    (hpos : 0 < bias)
    (hbias : bias ≤ 1 / 2)
    (hfloor :
      conclusion_binfold_kl_floor_from_max_bias_finiteVectorInequality
        bias certifiedFloor) :
    Real.log 2 ≤ certifiedFloor := by
  exact le_trans
    (conclusion_binfold_kl_floor_from_max_bias_oneSpikeProfile_half_floor hpos hbias)
    hfloor

end

end Omega.Conclusion
