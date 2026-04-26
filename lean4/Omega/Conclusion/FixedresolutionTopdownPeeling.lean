import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- The residual moment sequence after peeling the last `r` fixed-resolution layers. -/
noncomputable def conclusion_fixedresolution_topdown_peeling_residual
    (s : ℕ) (δ μ : ℕ → ℝ) (r q : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (s - r), μ j * δ j ^ q

/-- Paper label: `thm:conclusion-fixedresolution-topdown-peeling`. -/
theorem paper_conclusion_fixedresolution_topdown_peeling (s : ℕ) (δ μ : ℕ → ℝ) :
    ∀ r ≤ s, ∀ q : ℕ,
      conclusion_fixedresolution_topdown_peeling_residual s δ μ r q =
        ∑ j ∈ Finset.Icc 1 (s - r), μ j * δ j ^ q := by
  intro r _ q
  rfl

end Omega.Conclusion
