import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-strip-fourlayer-partition`. The four consecutive
hidden strips exactly partition the first `64` dyadic positions. -/
theorem paper_conclusion_window6_hidden_strip_fourlayer_partition :
    (((Finset.Icc 0 20 ∪ Finset.Icc 21 33) ∪ Finset.Icc 34 54) ∪ Finset.Icc 55 63 : Finset ℕ) =
      Finset.Icc 0 63 := by
  native_decide

end Omega.Conclusion
