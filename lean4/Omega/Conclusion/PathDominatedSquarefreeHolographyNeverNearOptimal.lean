import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-path-dominated-squarefree-holography-never-near-optimal`. -/
theorem paper_conclusion_path_dominated_squarefree_holography_never_near_optimal
    (supportSize Lmax Lopt : Nat -> Real) (hsupport : ∀ᶠ ν in Filter.atTop, 1 < supportSize ν)
    (hopt : ∀ᶠ ν in Filter.atTop, 0 < Lopt ν)
    (hgap : ∃ c > 0, ∀ᶠ ν in Filter.atTop, c * Real.log (supportSize ν) * Lopt ν <= Lmax ν) :
    ∃ c > 0, ∀ᶠ ν in Filter.atTop, c * Real.log (supportSize ν) <= Lmax ν / Lopt ν := by
  rcases hgap with ⟨c, hc, hgap⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsupport, hopt, hgap] with ν _ hoptν hgapν
  exact (le_div_iff₀ hoptν).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hgapν)

end Omega.Conclusion
