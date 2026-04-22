import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FiberRamanujanShadowCapacityReconstruction

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- The histogram-layer regrouping of the logarithmic volume/FK-determinant exponent recovered
from the Ramanujan shadow. -/
noncomputable def conclusion_center_top_fkdet_ramanujan_reconstruction_fkdet_log
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data) : ℝ :=
  Finset.sum (Finset.range D.maxFiberSize) fun s =>
    (conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s : ℝ) *
      Real.log (Nat.factorial (s + 1))

/-- Paper label: `thm:conclusion-center-top-fkdet-ramanujan-reconstruction`. The existing
Ramanujan-shadow reconstruction recovers the histogram layers, the top layer `M` is the largest
nonzero recovered layer once the higher layers vanish, `K` is the nonzero multiplicity on that top
layer, and the logarithmic FK-determinant exponent may be written equally with the shadow or the
recovered histogram. -/
theorem paper_conclusion_center_top_fkdet_ramanujan_reconstruction
    (D : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_data)
    (M : ℕ) (K : ℤ)
    (hTop :
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D M = K)
    (hK : K ≠ 0)
    (hAbove : ∀ s, M < s →
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D s = 0) :
    (∀ s,
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D s =
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s) ∧
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D M = K ∧
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D M ≠ 0 ∧
      (∀ s, M < s →
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s = 0) ∧
      (∀ s,
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s ≠ 0 →
          s ≤ M) ∧
      conclusion_center_top_fkdet_ramanujan_reconstruction_fkdet_log D =
        Finset.sum (Finset.range D.maxFiberSize) fun s =>
          (conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D s : ℝ) *
            Real.log (Nat.factorial (s + 1)) := by
  have hrecover :
      ∀ s,
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D s =
          conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s :=
    (paper_conclusion_fiber_ramanujan_shadow_capacity_reconstruction D).2.1
  have hshadowTop :
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D M = K := by
    calc
      conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D M
          =
            conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D M := by
              symm
              exact hrecover M
      _ = K := hTop
  refine ⟨hrecover, ?_, ?_, ?_, ?_, ?_⟩
  · exact hshadowTop
  · intro hzero
    exact hK (by simpa [hshadowTop] using hzero)
  · intro s hs
    have hzero : conclusion_fiber_ramanujan_shadow_capacity_reconstruction_recovered_histogram D s = 0 :=
      hAbove s hs
    simpa [hrecover s] using hzero
  · intro s hsNonzero
    by_contra hs
    have hgt : M < s := lt_of_not_ge hs
    have hzero :
        conclusion_fiber_ramanujan_shadow_capacity_reconstruction_shadow_histogram D s = 0 := by
      simpa [hrecover s] using hAbove s hgt
    exact hsNonzero hzero
  · unfold conclusion_center_top_fkdet_ramanujan_reconstruction_fkdet_log
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [← hrecover s]

end Omega.Conclusion
