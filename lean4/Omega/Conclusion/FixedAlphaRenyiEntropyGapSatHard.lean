import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete certificate for the fixed-alpha Renyi entropy SAT gap.  The field
`conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace` is the logarithm of the
alpha trace power, so the entropy below is the standard
`(1 / (1 - alpha)) * logTrace` expression. -/
structure conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data where
  Instance : Type u
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha : ℝ
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha_gt_one :
    1 < conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_isSat : Instance → Prop
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace : Instance → ℝ
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_entropyApprox : Instance → ℝ
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_unsatLogTrace :
    ∀ inst, ¬ conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_isSat inst →
      conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace inst =
        (1 - conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha) * Real.log 2
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_satLogTrace :
    ∀ inst, conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_isSat inst →
      conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace inst = 0
  conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_halfLogApprox :
    ∀ inst,
      |conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_entropyApprox inst -
        (1 / (1 - conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha)) *
          conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace inst| <
        Real.log 2 / 2

namespace conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data

/-- The fixed-alpha Renyi entropy obtained by unfolding the logarithmic trace formula. -/
noncomputable def renyiEntropy (D : conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data)
    (inst : D.Instance) : ℝ :=
  (1 / (1 - D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha)) *
    D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_logTrace inst

/-- A half-log-two additive approximation separates SAT from UNSAT. -/
def statement (D : conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data) : Prop :=
  ∀ inst,
    D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_entropyApprox inst < Real.log 2 / 2 ↔
      D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_isSat inst

end conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data

/-- Paper label: `cor:conclusion-fixed-alpha-renyi-entropy-gap-sat-hard`. -/
theorem paper_conclusion_fixed_alpha_renyi_entropy_gap_sat_hard
    (D : conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data) : D.statement := by
  intro inst
  constructor
  · intro happrox
    by_contra hnot
    have halpha_ne :
        1 - D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha ≠ 0 := by
      linarith [D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_alpha_gt_one]
    have hentropy :
        D.renyiEntropy inst = Real.log 2 := by
      rw [conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data.renyiEntropy,
        D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_unsatLogTrace inst hnot]
      field_simp [halpha_ne]
    have hclose :=
      D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_halfLogApprox inst
    rw [← conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data.renyiEntropy,
      hentropy] at hclose
    have hlower := (abs_lt.mp hclose).1
    linarith
  · intro hsat
    have hentropy : D.renyiEntropy inst = 0 := by
      rw [conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data.renyiEntropy,
        D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_satLogTrace inst hsat]
      ring
    have hclose :=
      D.conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_halfLogApprox inst
    rw [← conclusion_fixed_alpha_renyi_entropy_gap_sat_hard_data.renyiEntropy,
      hentropy] at hclose
    simpa using (abs_lt.mp hclose).2

end Omega.Conclusion
