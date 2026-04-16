import Mathlib.Tactic

namespace Omega.Folding

/-- The `u = 1` specialization of the gauge-anomaly quartic discriminant. -/
def gaugeAnomalyLeyangDiscriminantAtU1 (p : ℚ) : ℚ :=
  4 * (p + 1) ^ 2 * (2 * p - 1) ^ 2 * (p ^ 2 - p + 1) ^ 2

/-- Candidate Lee-Yang branch points at `u = 1` are exactly the zeros of the discriminant. -/
def gaugeAnomalyLeyangBranchPointCandidateAtU1 (p : ℚ) : Prop :=
  gaugeAnomalyLeyangDiscriminantAtU1 p = 0

private theorem gaugeAnomalyLeyang_quadratic_factor_pos (p : ℚ) : 0 < p ^ 2 - p + 1 := by
  have hsquare : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg (p - 1 / 2)
  nlinarith

set_option maxHeartbeats 400000 in
/-- Paper-facing `u = 1` Lee-Yang branch classification: on the Bernoulli window `p ∈ (0,1)`,
the explicit discriminant factorization forces the only branch-point candidate to occur at
`p = 1 / 2`.
    prop:fold-gauge-anomaly-bernoulli-p-leyang-branch-u1 -/
theorem paper_fold_gauge_anomaly_bernoulli_p_leyang_branch_u1
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    gaugeAnomalyLeyangBranchPointCandidateAtU1 p ↔ p = 1 / 2 := by
  unfold gaugeAnomalyLeyangBranchPointCandidateAtU1 gaugeAnomalyLeyangDiscriminantAtU1
  have hpPlusOne : 0 < p + 1 := by linarith
  have hquad : 0 < p ^ 2 - p + 1 := gaugeAnomalyLeyang_quadratic_factor_pos p
  have hleft : 0 < (p + 1) ^ 2 := sq_pos_of_pos hpPlusOne
  have hright : 0 < (p ^ 2 - p + 1) ^ 2 := sq_pos_of_pos hquad
  constructor
  · intro hdisc
    have hmid :
        (4 * (p + 1) ^ 2 * (p ^ 2 - p + 1) ^ 2) * (2 * p - 1) ^ 2 = 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdisc
    have hcoeff :
        4 * (p + 1) ^ 2 * (p ^ 2 - p + 1) ^ 2 ≠ 0 := by
      have hpos : 0 < 4 * (p + 1) ^ 2 * (p ^ 2 - p + 1) ^ 2 := by
        positivity
      linarith
    have hsq : (2 * p - 1) ^ 2 = 0 := (mul_eq_zero.mp hmid).resolve_left hcoeff
    have hlin : 2 * p - 1 = 0 := by
      have hsnonneg : 0 ≤ (2 * p - 1) ^ 2 := sq_nonneg (2 * p - 1)
      nlinarith
    linarith
  · intro hpHalf
    subst hpHalf
    norm_num

end Omega.Folding
