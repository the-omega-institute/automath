import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Omega.Conclusion.CollisionMomentStieltjesHankelPositivity
import Omega.Conclusion.FoldOutputEntropyGaugeAffineIdentity

open Filter Topology

namespace Omega.Conclusion

/-- The logarithmic high-moment upper envelope appearing in the gauge-density estimate. -/
noncomputable def conclusion_gauge_density_highmoment_dominance_bound
    (S : ℕ → ℝ) (q m : ℕ) : ℝ :=
  Real.log (S m / ((2 : ℝ) ^ m)) / ((q : ℝ) - 1) - 1

/-- Concrete package for the high-moment dominance principle: rewriting the logarithmic term through
`S_q(m) / 2^m` gives the finite-volume upper envelope, and any pointwise dominance by that envelope
passes to the limiting inequality. -/
def conclusion_gauge_density_highmoment_dominance_package (g S : ℕ → ℝ) (q : ℕ) : Prop :=
  (∀ m : ℕ,
      2 ≤ q →
      0 < S m →
      g m ≤ (Real.log (S m) - Real.log ((2 : ℝ) ^ m)) / ((q : ℝ) - 1) - 1 →
      g m ≤ conclusion_gauge_density_highmoment_dominance_bound S q m) ∧
    (∀ G P : ℝ,
      2 ≤ q →
      (∀ m : ℕ, g m ≤ conclusion_gauge_density_highmoment_dominance_bound S q m) →
      Tendsto (fun m : ℕ => conclusion_gauge_density_highmoment_dominance_bound S q m) atTop (𝓝 P) →
      Tendsto g atTop (𝓝 G) →
      G ≤ P)

/-- Paper label: `thm:conclusion-gauge-density-highmoment-dominance`. Rewriting the logarithmic
envelope through `S_q(m) / 2^m` is immediate from `log (a / b) = log a - log b`, and the limiting
upper bound is the standard order-preservation of limits under pointwise domination. -/
theorem paper_conclusion_gauge_density_highmoment_dominance
    (g S : ℕ → ℝ) (q : ℕ) : conclusion_gauge_density_highmoment_dominance_package g S q := by
  refine ⟨?_, ?_⟩
  · intro m _hq hS hg
    unfold conclusion_gauge_density_highmoment_dominance_bound
    have hpow_ne : ((2 : ℝ) ^ m) ≠ 0 := by positivity
    simpa [Real.log_div hS.ne' hpow_ne] using hg
  · intro G P _hq hdom hbound hg
    exact le_of_tendsto_of_tendsto' hg hbound hdom

end Omega.Conclusion
