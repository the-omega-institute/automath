import Mathlib.Tactic

namespace Omega.POM

/-- Publication-facing likelihood-ratio monotonicity for a biased posterior family.
    prop:pom-fiber-biased-posterior-mlr -/
theorem paper_pom_fiber_biased_posterior_mlr
    (tp tq Zp Zq : ℝ) (ht : 1 < tp / tq) (hscale : 0 < Zq / Zp) :
    StrictMono (fun r : ℕ => (tp / tq) ^ r * (Zq / Zp)) := by
  intro a b hab
  have hpow : (tp / tq) ^ a < (tp / tq) ^ b := pow_lt_pow_right₀ ht hab
  exact mul_lt_mul_of_pos_right hpow hscale

end Omega.POM
