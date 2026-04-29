import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic
import Omega.Conclusion.Window6HiddenStripFourlayerPartition

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-window6-e64-finite-borel-partition`. -/
theorem paper_conclusion_window6_e64_finite_borel_partition (t : ℂ) :
    (Finset.range 64).sum (fun n => t ^ n / (Nat.factorial n : ℂ)) =
      (Finset.Icc 0 20).sum (fun n => t ^ n / (Nat.factorial n : ℂ)) +
      (Finset.Icc 21 33).sum (fun n => t ^ n / (Nat.factorial n : ℂ)) +
      (Finset.Icc 34 54).sum (fun n => t ^ n / (Nat.factorial n : ℂ)) +
      (Finset.Icc 55 63).sum (fun n => t ^ n / (Nat.factorial n : ℂ)) := by
  let f : ℕ → ℂ := fun n => t ^ n / (Nat.factorial n : ℂ)
  change (Finset.range 64).sum f =
    (Finset.Icc 0 20).sum f + (Finset.Icc 21 33).sum f +
      (Finset.Icc 34 54).sum f + (Finset.Icc 55 63).sum f
  have hRange : Finset.range 64 = Finset.Icc 0 63 := by
    ext n
    simp [Finset.mem_Icc]
    omega
  rw [hRange]
  rw [← paper_conclusion_window6_hidden_strip_fourlayer_partition]
  have hdisj01 : Disjoint (Finset.Icc 0 20) (Finset.Icc 21 33) := by
    native_decide
  have hdisj012 : Disjoint (Finset.Icc 0 20 ∪ Finset.Icc 21 33) (Finset.Icc 34 54) := by
    native_decide
  have hdisj0123 :
      Disjoint ((Finset.Icc 0 20 ∪ Finset.Icc 21 33) ∪ Finset.Icc 34 54)
        (Finset.Icc 55 63) := by
    native_decide
  rw [Finset.sum_union hdisj0123, Finset.sum_union hdisj012, Finset.sum_union hdisj01]

/-- Paper label:
`cor:conclusion-window6-dyadic-geometric-series-hidden-strip-telescope`. -/
theorem paper_conclusion_window6_dyadic_geometric_series_hidden_strip_telescope (z : ℂ) :
    (Finset.range 64).sum (fun n => z ^ n) =
      (1 + z ^ 34) * (Finset.range 21).sum (fun n => z ^ n) +
        z ^ 21 * (Finset.range 13).sum (fun n => z ^ n) +
          z ^ 55 * (Finset.range 9).sum (fun n => z ^ n) := by
  norm_num [Finset.sum_range_succ]
  ring

end Omega.Conclusion
