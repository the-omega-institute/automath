import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.DeltaqGoldenEnvelope

namespace Omega.POM

/-- Paper label: `cor:pom-deltaq-gLambda-identity`. The collision exponent `δ_q` is obtained from
the logarithmic gap `g_q^(Λ)` by a direct logarithmic rewrite. -/
theorem paper_pom_deltaq_glambda_identity (rq Lambdaq : ℕ → ℝ) (q : ℕ) (hq : 2 ≤ q)
    (hLambda : 0 < Lambdaq q) (hrq : 0 < rq q) :
    let gLambda := (1 / (q : ℝ)) * Real.log (rq q / Lambdaq q)
    pomDeltaq rq Lambdaq q = Real.log (rq q) - 2 * (q : ℝ) * gLambda := by
  dsimp
  have hLambda_ne : Lambdaq q ≠ 0 := ne_of_gt hLambda
  have hrq_ne : rq q ≠ 0 := ne_of_gt hrq
  have hq_ne : (q : ℝ) ≠ 0 := by positivity
  unfold pomDeltaq
  rw [Real.log_div (pow_ne_zero 2 hLambda_ne) hrq_ne, Real.log_pow, Real.log_div hrq_ne hLambda_ne]
  field_simp [hq_ne]
  ring

end Omega.POM
