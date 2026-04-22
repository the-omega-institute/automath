import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite Blaschke data for the endpoint extreme-resonance criterion. -/
structure XiExtremeResonanceCriterionData where
  κ : ℕ
  gamma : Fin κ → ℝ
  delta : Fin κ → ℝ
  delta_nonneg : ∀ k, 0 ≤ delta k

/-- The individual endpoint Poisson contribution `P_{a_k}(-1)`. -/
def xiExtremeResonancePoissonTerm (D : XiExtremeResonanceCriterionData) (k : Fin D.κ) : ℝ :=
  4 * D.delta k / ((D.gamma k) ^ 2 + (1 + D.delta k) ^ 2)

/-- The appendix current `j_in(π)`. -/
def xiExtremeResonanceJinPi (D : XiExtremeResonanceCriterionData) : ℝ :=
  ∑ k, xiExtremeResonancePoissonTerm D k

/-- The endpoint potential `Φ_{-1}(B)`. -/
def xiExtremeResonancePhiMinusOne (D : XiExtremeResonanceCriterionData) : ℝ :=
  xiExtremeResonanceJinPi D

/-- The explicit Poisson expansion `Σ P_{a_k}(-1)`. -/
def xiExtremeResonancePoissonSum (D : XiExtremeResonanceCriterionData) : ℝ :=
  ∑ k, xiExtremeResonancePoissonTerm D k

/-- Total endpoint defect mass `Σ δ_k`. -/
def xiExtremeResonanceDeltaSum (D : XiExtremeResonanceCriterionData) : ℝ :=
  ∑ k, D.delta k

/-- Vanishing of every endpoint defect. -/
def xiExtremeResonanceAllDeltaZero (D : XiExtremeResonanceCriterionData) : Prop :=
  ∀ k, D.delta k = 0

private lemma xiExtremeResonancePoissonTerm_nonneg (D : XiExtremeResonanceCriterionData)
    (k : Fin D.κ) : 0 ≤ xiExtremeResonancePoissonTerm D k := by
  unfold xiExtremeResonancePoissonTerm
  have hnum_nonneg : 0 ≤ 4 * D.delta k := by
    nlinarith [D.delta_nonneg k]
  have hden_nonneg : 0 ≤ (D.gamma k) ^ 2 + (1 + D.delta k) ^ 2 := by positivity
  exact div_nonneg hnum_nonneg hden_nonneg

private lemma xiExtremeResonancePoissonTerm_pos {D : XiExtremeResonanceCriterionData}
    {k : Fin D.κ} (hk : 0 < D.delta k) : 0 < xiExtremeResonancePoissonTerm D k := by
  unfold xiExtremeResonancePoissonTerm
  have hden_pos : 0 < (D.gamma k) ^ 2 + (1 + D.delta k) ^ 2 := by
    have hone : 0 < 1 + D.delta k := by linarith [D.delta_nonneg k]
    positivity
  exact div_pos (by positivity) hden_pos

private lemma xiExtremeResonancePoissonTerm_le_four_mul_delta (D : XiExtremeResonanceCriterionData)
    (k : Fin D.κ) : xiExtremeResonancePoissonTerm D k ≤ 4 * D.delta k := by
  unfold xiExtremeResonancePoissonTerm
  let den : ℝ := (D.gamma k) ^ 2 + (1 + D.delta k) ^ 2
  have hden_ge_one : 1 ≤ den := by
    have hone_sq : 1 ≤ (1 + D.delta k) ^ 2 := by
      nlinarith [D.delta_nonneg k]
    dsimp [den]
    nlinarith
  have hbase : (4 * D.delta k) / den ≤ 4 * D.delta k := by
    exact div_le_self (by nlinarith [D.delta_nonneg k]) hden_ge_one
  simpa [den]
    using hbase

private lemma xiExtremeResonanceAllDeltaZero_of_jin_eq_zero (D : XiExtremeResonanceCriterionData)
    (hjin : xiExtremeResonanceJinPi D = 0) : xiExtremeResonanceAllDeltaZero D := by
  intro k
  by_cases hk : D.delta k = 0
  · exact hk
  · have hk_pos : 0 < D.delta k := lt_of_le_of_ne (D.delta_nonneg k) (Ne.symm hk)
    have hterm_pos : 0 < xiExtremeResonancePoissonTerm D k :=
      xiExtremeResonancePoissonTerm_pos hk_pos
    have hle :
        xiExtremeResonancePoissonTerm D k ≤ xiExtremeResonanceJinPi D := by
      unfold xiExtremeResonanceJinPi
      exact Finset.single_le_sum
        (fun i _ => xiExtremeResonancePoissonTerm_nonneg D i) (by simp)
    have hsum_pos : 0 < xiExtremeResonanceJinPi D :=
      lt_of_lt_of_le hterm_pos hle
    linarith

private lemma xiExtremeResonanceAllDeltaZero_iff_deltaSum_eq_zero (D : XiExtremeResonanceCriterionData) :
    xiExtremeResonanceAllDeltaZero D ↔ xiExtremeResonanceDeltaSum D = 0 := by
  constructor
  · intro hzero
    unfold xiExtremeResonanceDeltaSum
    refine Finset.sum_eq_zero ?_
    intro k hk
    exact hzero k
  · intro hsum k
    by_cases hk : D.delta k = 0
    · exact hk
    · have hk_pos : 0 < D.delta k := lt_of_le_of_ne (D.delta_nonneg k) (Ne.symm hk)
      have hle : D.delta k ≤ xiExtremeResonanceDeltaSum D := by
        unfold xiExtremeResonanceDeltaSum
        exact Finset.single_le_sum (fun i _ => D.delta_nonneg i) (by simp)
      have hsum_pos : 0 < xiExtremeResonanceDeltaSum D := lt_of_lt_of_le hk_pos hle
      linarith

/-- Paper-facing criterion for the extreme-resonance endpoint current. The appendix identity
`j_in(π) = Φ_{-1}(B) = Σ P_{a_k}(-1)` is encoded literally, positivity of every Poisson term turns
vanishing into three equivalent conditions, and the explicit endpoint-current inequality yields the
linear bound `j_in(π) / 4 ≤ Σ δ_k`. -/
def XiExtremeResonanceCriterionStatement (D : XiExtremeResonanceCriterionData) : Prop :=
  xiExtremeResonanceJinPi D = xiExtremeResonancePhiMinusOne D ∧
    xiExtremeResonancePhiMinusOne D = xiExtremeResonancePoissonSum D ∧
    (xiExtremeResonanceJinPi D = 0 ↔ xiExtremeResonanceAllDeltaZero D) ∧
    (xiExtremeResonanceAllDeltaZero D ↔ xiExtremeResonanceDeltaSum D = 0) ∧
    (xiExtremeResonanceJinPi D = 0 ↔ xiExtremeResonanceDeltaSum D = 0) ∧
    xiExtremeResonanceJinPi D / 4 ≤ xiExtremeResonanceDeltaSum D

/-- Paper label: `cor:xi-extreme-resonance-criterion`. -/
theorem paper_xi_extreme_resonance_criterion
    (D : XiExtremeResonanceCriterionData) : XiExtremeResonanceCriterionStatement D := by
  have hdelta :
      xiExtremeResonanceAllDeltaZero D ↔ xiExtremeResonanceDeltaSum D = 0 :=
    xiExtremeResonanceAllDeltaZero_iff_deltaSum_eq_zero D
  have hjin_zero :
      xiExtremeResonanceJinPi D = 0 ↔ xiExtremeResonanceAllDeltaZero D := by
    constructor
    · exact xiExtremeResonanceAllDeltaZero_of_jin_eq_zero D
    · intro hzero
      unfold xiExtremeResonanceJinPi xiExtremeResonancePoissonTerm
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [hzero k]
  have hbound :
      xiExtremeResonanceJinPi D ≤ 4 * xiExtremeResonanceDeltaSum D := by
    calc
      xiExtremeResonanceJinPi D = ∑ k, xiExtremeResonancePoissonTerm D k := rfl
      _ ≤ ∑ k, 4 * D.delta k := by
        exact Finset.sum_le_sum (fun k _ => xiExtremeResonancePoissonTerm_le_four_mul_delta D k)
      _ = 4 * xiExtremeResonanceDeltaSum D := by
        simp [xiExtremeResonanceDeltaSum, Finset.mul_sum]
  refine ⟨rfl, rfl, hjin_zero, hdelta, hjin_zero.trans hdelta, ?_⟩
  nlinarith

end

end Omega.Zeta
