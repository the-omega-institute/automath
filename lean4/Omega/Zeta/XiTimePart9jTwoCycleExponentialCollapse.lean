import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9j-two-cycle-exponential-collapse`. -/
theorem paper_xi_time_part9j_two_cycle_exponential_collapse (ε : ℝ)
    (agreeProb : ℕ → ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hnonneg : ∀ T, 0 ≤ agreeProb T)
    (hbound : ∀ T, agreeProb T ≤ (1 - ε) ^ (T / 2)) :
    (∀ T, agreeProb T ≤ (1 - ε) ^ (T / 2)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ T0 : ℕ, ∀ T ≥ T0, agreeProb T < δ) := by
  constructor
  · exact hbound
  · intro δ hδ
    have hbase_nonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
    have hbase_le_one : 1 - ε ≤ 1 := by linarith
    have hbase_lt_one : 1 - ε < 1 := by linarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hbase_lt_one
    refine ⟨2 * n, ?_⟩
    intro T hT
    have hn_le_half : n ≤ T / 2 := by
      refine (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 ?_
      nlinarith [hT]
    have htail : (1 - ε) ^ (T / 2) ≤ (1 - ε) ^ n :=
      pow_le_pow_of_le_one hbase_nonneg hbase_le_one hn_le_half
    have _hprob_nonneg : 0 ≤ agreeProb T := hnonneg T
    exact lt_of_le_of_lt ((hbound T).trans htail) hn

end Omega.Zeta
