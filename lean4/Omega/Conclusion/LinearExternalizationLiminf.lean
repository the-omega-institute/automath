import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Omega.Conclusion

open Filter

/-- Concrete lower-tail data for the linear externalization argument.  For each rational threshold
`q`, `gaugeTailProb q m` bounds the probability of the transferred gauge event
`G_m / m ≤ R * q`, `rewriteTailProb q m` bounds the rewrite event `T_m / m ≤ q`, and
Borel-Cantelli is recorded through the concrete family `eventuallyAbove q`. -/
structure LinearExternalizationLiminfData where
  R : ℝ
  rewriteTailProb : ℚ → ℕ → ℝ
  gaugeTailProb : ℚ → ℕ → ℝ
  eventuallyAbove : ℚ → Prop
  hR : 0 < R
  rewrite_le_gauge : ∀ q m, rewriteTailProb q m ≤ gaugeTailProb q m
  gaugeExponential : ∀ q : ℚ, (q : ℝ) < 4 / (9 * R) →
    ∃ c > 0, ∀ᶠ m in atTop, gaugeTailProb q m ≤ Real.exp (-c * m)
  summable_of_exponential : ∀ q : ℚ,
    (∃ c > 0, ∀ᶠ m in atTop, rewriteTailProb q m ≤ Real.exp (-c * m)) →
      Summable (rewriteTailProb q)
  borelCantelli : ∀ q : ℚ, Summable (rewriteTailProb q) → eventuallyAbove q

namespace LinearExternalizationLiminfData

/-- Every rational threshold below `4 / (9R)` has an exponential lower-tail bound for
`T_m / m`. -/
def exponentialLowerTail (D : LinearExternalizationLiminfData) : Prop :=
  ∀ q : ℚ, (q : ℝ) < 4 / (9 * D.R) →
    ∃ c > 0, ∀ᶠ m in atTop, D.rewriteTailProb q m ≤ Real.exp (-c * m)

/-- Every rational threshold below `4 / (9R)` is eventually violated almost surely, which is the
countable Borel-Cantelli packaging of the liminf lower bound. -/
def aeLiminfLowerBound (D : LinearExternalizationLiminfData) : Prop :=
  ∀ q : ℚ, (q : ℝ) < 4 / (9 * D.R) → D.eventuallyAbove q

end LinearExternalizationLiminfData

/-- The lower-tail estimate for `G_m / m` transfers through `G_m ≤ R T_m`, and the resulting
summable rational thresholds yield the almost-sure lower bound via Borel-Cantelli.
    thm:conclusion-linear-externalization-liminf -/
theorem paper_conclusion_linear_externalization_liminf (D : LinearExternalizationLiminfData) :
    D.aeLiminfLowerBound ∧ D.exponentialLowerTail := by
  have hExp : D.exponentialLowerTail := by
    intro q hq
    rcases D.gaugeExponential q hq with ⟨c, hc, htail⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [htail] with m hm
    exact le_trans (D.rewrite_le_gauge q m) hm
  have hAe : D.aeLiminfLowerBound := by
    intro q hq
    have hRewriteExp : ∃ c > 0, ∀ᶠ m in atTop, D.rewriteTailProb q m ≤ Real.exp (-c * m) :=
      hExp q hq
    exact D.borelCantelli q (D.summable_of_exponential q hRewriteExp)
  exact ⟨hAe, hExp⟩

end Omega.Conclusion
