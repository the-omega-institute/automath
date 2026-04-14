import Mathlib.Tactic
import Omega.CircleDimension.ResidualCircleDim

namespace Omega.CircleDimension.BareCircleNotCompleteCarrier

/-- The model residual register `t * 2^(b*(r-1))` has discrete residual circle-dimension
    at least `r - 1` at depth `b`.
    cor:cdim-bare-circle-not-complete-carrier -/
theorem residualCdimAt_lower_bound
    (t b r : ℕ) (ht : 1 ≤ t) (hb : 0 < b) :
    r - 1 ≤
      Omega.CircleDimension.residualCdimAt
        (fun n => t * 2 ^ (n * (r - 1))) b := by
  unfold Omega.CircleDimension.residualCdimAt
  have hmul :
      2 ^ (b * (r - 1)) ≤ t * 2 ^ (b * (r - 1)) := by
    simpa using Nat.mul_le_mul_right (2 ^ (b * (r - 1))) ht
  have hlog :
      Nat.log 2 (2 ^ (b * (r - 1))) ≤
        Nat.log 2 (t * 2 ^ (b * (r - 1))) := by
    exact Nat.log_mono_right hmul
  have hdiv :
      Nat.log 2 (2 ^ (b * (r - 1))) / b ≤
        Nat.log 2 (t * 2 ^ (b * (r - 1))) / b := by
    exact Nat.div_le_div_right (c := b) hlog
  simpa [Nat.log_pow (by norm_num : 1 < 2), Nat.mul_div_right _ hb]
    using hdiv

/-- Paper seed: a single visible circle channel forces an exponential residual register,
    hence a residual circle-dimension budget of at least `r - 1`.
    cor:cdim-bare-circle-not-complete-carrier -/
theorem paper_cdim_bare_circle_not_complete_carrier_seeds
    (b r t R : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hb : 0 < b)
    (hinj : ∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ b) * R), Function.Injective f) :
    t * 2 ^ (b * (r - 1)) ≤ R ∧
      r - 1 ≤
        Omega.CircleDimension.residualCdimAt
          (fun n => t * 2 ^ (n * (r - 1))) b ∧
      (2 ≤ r →
        0 <
          Omega.CircleDimension.residualCdimAt
            (fun n => t * 2 ^ (n * (r - 1))) b) := by
  refine ⟨Omega.CircleDimension.paper_cdim_single_circle_exponential_residual b r t R hr hinj, ?_,
    ?_⟩
  · exact residualCdimAt_lower_bound t b r ht hb
  · intro hr2
    have hlower := residualCdimAt_lower_bound t b r ht hb
    have hpos : 0 < r - 1 := by omega
    exact lt_of_lt_of_le hpos hlower

end Omega.CircleDimension.BareCircleNotCompleteCarrier
