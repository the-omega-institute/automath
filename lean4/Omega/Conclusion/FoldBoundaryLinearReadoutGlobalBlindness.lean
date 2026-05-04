import Mathlib.Tactic
import Omega.Core.WalshFourier
import Omega.Folding.Fiber

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The prefixed fiberwise Walsh sum used in
`cor:conclusion-fold-boundary-linear-readout-global-blindness`. -/
def conclusion_fold_boundary_linear_readout_global_blindness_walsh
    {m : ℕ} (I : Finset (Fin m)) (x : Omega.X m) : ℤ :=
  ∑ w ∈ Omega.X.fiber x, Omega.Core.walshChar I w

/-- Paper label: `cor:conclusion-fold-boundary-linear-readout-global-blindness`.
Summing any nonempty Walsh character over all fold fibers cancels globally, while the empty
character counts the whole word cube. -/
theorem paper_conclusion_fold_boundary_linear_readout_global_blindness
    (m : ℕ) (I : Finset (Fin m)) :
    (∑ x : Omega.X m,
        conclusion_fold_boundary_linear_readout_global_blindness_walsh (m := m) I x) =
      if I = ∅ then (2 ^ m : ℤ) else 0 := by
  classical
  have hfiber :
      (∑ x : Omega.X m,
          conclusion_fold_boundary_linear_readout_global_blindness_walsh (m := m) I x) =
        ∑ w : Omega.Word m, Omega.Core.walshChar I w := by
    simpa [conclusion_fold_boundary_linear_readout_global_blindness_walsh, Omega.X.fiber] using
      (Finset.sum_fiberwise_eq_sum_filter
        (s := (Finset.univ : Finset (Omega.Word m)))
        (t := (Finset.univ : Finset (Omega.X m)))
        (g := Omega.Fold)
        (f := fun w : Omega.Word m => Omega.Core.walshChar I w))
  have horth :
      (∑ w : Omega.Word m, Omega.Core.walshChar I w) =
        if I = ∅ then (2 ^ m : ℤ) else 0 := by
    simpa using (Omega.Core.walshChar_orthogonal_sum I ∅)
  exact hfiber.trans horth

end

end Omega.Conclusion
