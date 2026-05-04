import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-exact-k-ambiguity-exposed-phase`. -/
theorem paper_conclusion_exact_k_ambiguity_exposed_phase (exact tail next scale : ℕ → ℝ)
    (C : ℝ) (hExact : ∀ n, exact n = tail n - next n)
    (htail : Tendsto (fun n => tail n / scale n) atTop (𝓝 C))
    (hnext : Tendsto (fun n => next n / scale n) atTop (𝓝 0)) :
    Tendsto (fun n => exact n / scale n) atTop (𝓝 C) := by
  have hlim : Tendsto (fun n => tail n / scale n - next n / scale n) atTop (𝓝 (C - 0)) :=
    htail.sub hnext
  simpa using hlim.congr' (Filter.Eventually.of_forall fun n => by
    rw [hExact n]
    ring)

end Omega.Conclusion
