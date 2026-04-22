import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.BernoulliPBitpairLaw

namespace Omega.Folding

/-- Paper label: `thm:fold-bernoulli-p-bitpair-gamma-q-closed`. -/
theorem paper_fold_bernoulli_p_bitpair_gamma_q_closed (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let q00 := (1 - p - p ^ 2 + 2 * p ^ 3 - p ^ 4) / (1 + p ^ 3)
    let q01 := (p ^ 2 * (1 - p)) / (1 + p ^ 3)
    let q10 := (p ^ 2 * (2 - p)) / (1 + p ^ 3)
    let q11 := (p * (p ^ 3 + (1 - p) ^ 2)) / (1 + p ^ 3)
    let γ := q01 + q10
    let q := q01 + q11
    γ = p ^ 2 * (3 - 2 * p) / (1 + p ^ 3) ∧
      q = p * (p ^ 3 - p + 1) / (1 + p ^ 3) ∧
      (0 < p → p < 1 → 0 < q ∧ q < p) := by
  dsimp
  have hden : (1 + p ^ 3 : ℝ) ≠ 0 := by positivity
  rcases paper_fold_gauge_anomaly_bernoulli_p_bitpair_law p hp0 hp1 with
    ⟨_, hp_minus_q, hgamma⟩
  have hq_closed :
      (p ^ 2 * (1 - p)) / (1 + p ^ 3) + (p * (p ^ 3 + (1 - p) ^ 2)) / (1 + p ^ 3) =
        p * (p ^ 3 - p + 1) / (1 + p ^ 3) := by
    field_simp [hden]
    ring_nf
  refine ⟨hgamma, hq_closed, ?_⟩
  intro hp_pos hp_lt_one
  have hp_sq_pos : 0 < p ^ 2 := by nlinarith
  have hp3_nonneg : 0 ≤ p ^ 3 := by positivity
  have hden_pos : 0 < (1 + p ^ 3 : ℝ) := by linarith
  have hfrac_pos : 0 < p ^ 2 / (1 + p ^ 3) := div_pos hp_sq_pos hden_pos
  have hp_sq_lt_p : p ^ 2 < p := by nlinarith
  have hp3_pos : 0 < p ^ 3 := by positivity
  have hp_lt_mul : p < p * (1 + p ^ 3) := by
    have hone_lt : (1 : ℝ) < 1 + p ^ 3 := by linarith
    simpa [mul_assoc] using (mul_lt_mul_of_pos_left hone_lt hp_pos)
  have hfrac_lt_p : p ^ 2 / (1 + p ^ 3) < p := by
    rw [div_lt_iff₀ hden_pos]
    exact lt_trans hp_sq_lt_p hp_lt_mul
  constructor
  · nlinarith [hp_minus_q, hfrac_lt_p]
  · nlinarith [hp_minus_q, hfrac_pos]

end Omega.Folding
