import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The positive correction term that is lost when diagonal uniformization is forced at error level
`δ`. -/
noncomputable def uniformDiagonalPenalty (δ : ℝ) : ℝ :=
  δ * (1 - δ)

/-- A simple closed-form uniform diagonal rate: the ambient alphabet contributes `log n`, while the
uniformity correction contributes the positive quadratic defect `δ(1-δ)`. -/
noncomputable def uniformDiagonalRate (n : ℕ) (δ : ℝ) : ℝ :=
  Real.log (n : ℝ) + uniformDiagonalPenalty δ

private lemma log_nat_pow (n k : ℕ) (hn : 0 < n) :
    Real.log ((n ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log (n : ℝ) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
      have hpow_real : 0 < ((n ^ k : ℕ) : ℝ) := by
        exact_mod_cast pow_pos hn k
      rw [Nat.pow_succ, Nat.cast_mul, Real.log_mul hpow_real.ne' hn_real.ne', ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- The diagonal uniform rate is strictly subadditive under `k`-fold blocking: the ambient
logarithmic term scales linearly, while the positive uniformity correction appears only once on the
left but `k` times on the right.
    thm:pom-diagonal-rate-uniform-synergy-inequality -/
theorem paper_pom_diagonal_rate_uniform_synergy_inequality (n k : ℕ) (δ : ℝ) (hn : 2 ≤ n)
    (hk : 2 ≤ k) (hδ0 : 0 < δ) (hδ1 : δ < 1 - (1 : ℝ) / (n ^ k : ℝ)) :
    uniformDiagonalRate (n ^ k) δ < (k : ℝ) * uniformDiagonalRate n δ := by
  have hn_pos : 0 < n := by omega
  have hnk_pos_nat : 0 < n ^ k := by exact pow_pos hn_pos k
  have hnk_pos : 0 < (n ^ k : ℝ) := by exact_mod_cast hnk_pos_nat
  have hfrac_pos : 0 < (1 : ℝ) / (n ^ k : ℝ) := by positivity
  have hδ_lt_one : δ < 1 := by linarith
  have hpenalty_pos : 0 < uniformDiagonalPenalty δ := by
    unfold uniformDiagonalPenalty
    nlinarith
  have hk_gt_one : (1 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hk)
  have hpenalty_lt :
      uniformDiagonalPenalty δ < (k : ℝ) * uniformDiagonalPenalty δ := by
    nlinarith
  have hleft :
      uniformDiagonalRate (n ^ k) δ = (k : ℝ) * Real.log (n : ℝ) + uniformDiagonalPenalty δ := by
    unfold uniformDiagonalRate
    rw [log_nat_pow n k hn_pos]
  have hright :
      (k : ℝ) * uniformDiagonalRate n δ =
        (k : ℝ) * Real.log (n : ℝ) + (k : ℝ) * uniformDiagonalPenalty δ := by
    unfold uniformDiagonalRate
    ring
  rw [hleft, hright]
  have hstrict :
      (k : ℝ) * Real.log (n : ℝ) + uniformDiagonalPenalty δ <
        (k : ℝ) * Real.log (n : ℝ) + (k : ℝ) * uniformDiagonalPenalty δ := by
    linarith
  exact hstrict

end Omega.POM
