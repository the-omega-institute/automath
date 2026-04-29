import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Deterministic Chebotarev tail term `A / λ^(α n)`. -/
def auditableProfiniteChebotarevDeterministicTerm (A alpha lambda n : ℝ) : ℝ :=
  A / lambda ^ (alpha * n)

/-- Sampling term `B / √N` after packaging the explicit TV-envelope constants into `B`. -/
def auditableProfiniteChebotarevSamplingTerm (B N : ℝ) : ℝ :=
  B / Real.sqrt N

/-- Closed-form sample size obtained by balancing `A / λ^(α n)` against `B / √N`. -/
def auditableProfiniteChebotarevBalancedSampleSize (A B alpha lambda n : ℝ) : ℝ :=
  (B * lambda ^ (alpha * n) / A) ^ (2 : Nat)

/-- Closed-form depth obtained by solving the same balance relation for `n`. -/
def auditableProfiniteChebotarevBalancedDepth (A B alpha lambda N : ℝ) : ℝ :=
  (Real.log A - Real.log B + (1 / 2 : ℝ) * Real.log N) / (alpha * Real.log lambda)

set_option maxHeartbeats 400000 in
/-- Paper label: `cor:auditable-profinite-chebotarev-tradeoff`.
After packaging the deterministic term and the sampling prefactor as positive constants `A` and
`B`, the balance equation `A / λ^(α n) = B / √N` can be solved exactly: once for the balanced
sample size, and once for the corresponding depth by taking logarithms. -/
theorem paper_auditable_profinite_chebotarev_tradeoff
    {A B alpha lambda n N : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hlambda : 0 < lambda) (halpha : alpha ≠ 0)
    (hlog : Real.log lambda ≠ 0)
    (hbalance :
      auditableProfiniteChebotarevDeterministicTerm A alpha lambda n =
        auditableProfiniteChebotarevSamplingTerm B N)
    (hN : 0 < N) :
    auditableProfiniteChebotarevDeterministicTerm A alpha lambda n =
      auditableProfiniteChebotarevSamplingTerm B
        (auditableProfiniteChebotarevBalancedSampleSize A B alpha lambda n) ∧
      n = auditableProfiniteChebotarevBalancedDepth A B alpha lambda N := by
  constructor
  · unfold auditableProfiniteChebotarevDeterministicTerm auditableProfiniteChebotarevSamplingTerm
      auditableProfiniteChebotarevBalancedSampleSize
    have hpow_pos : 0 < lambda ^ (alpha * n) := by
      exact Real.rpow_pos_of_pos hlambda _
    have hratio_pos : 0 < B * lambda ^ (alpha * n) / A := by
      positivity
    rw [Real.sqrt_sq_eq_abs]
    have habs : |B * lambda ^ (alpha * n) / A| = B * lambda ^ (alpha * n) / A := by
      exact abs_of_pos hratio_pos
    rw [habs]
    field_simp [hA.ne', hB.ne', hpow_pos.ne']
  · have hpow_pos : 0 < lambda ^ (alpha * n) := by
      exact Real.rpow_pos_of_pos hlambda _
    have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hsqrtN_ne : Real.sqrt N ≠ 0 := ne_of_gt hsqrtN_pos
    have hmain : A * Real.sqrt N = B * lambda ^ (alpha * n) := by
      unfold auditableProfiniteChebotarevDeterministicTerm
        auditableProfiniteChebotarevSamplingTerm at hbalance
      field_simp [hA.ne', hB.ne', hpow_pos.ne', hsqrtN_ne] at hbalance
      linarith
    have hlogeq :
        Real.log A + Real.log (Real.sqrt N) = Real.log B + alpha * n * Real.log lambda := by
      have := congrArg Real.log hmain
      rw [Real.log_mul hA.ne' hsqrtN_ne, Real.log_mul hB.ne' hpow_pos.ne',
        Real.log_rpow hlambda] at this
      exact this
    have hsqrt_log : Real.log (Real.sqrt N) = (1 / 2 : ℝ) * Real.log N := by
      rw [Real.log_sqrt hN.le]
      ring
    unfold auditableProfiniteChebotarevBalancedDepth
    have hdenom : alpha * Real.log lambda ≠ 0 := mul_ne_zero halpha hlog
    apply (eq_div_iff hdenom).2
    rw [hsqrt_log] at hlogeq
    linarith

end

end Omega.Zeta
