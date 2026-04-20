import Mathlib.Tactic
import Omega.GU.Window6B3SupportCount
import Omega.GU.Window6C3SupportCount

namespace Omega.GU

/-- The window-6 `B₃` and `C₃` Hilbert-twin supports have the same cardinality, so the degree-4
interpolation wrapper may be registered by rewriting both counts to `19`.
    cor:window6-b3c3-hilbert-twins-degree4-interpolation -/
theorem paper_window6_b3c3_hilbert_twins_degree4_interpolation :
    Omega.GU.Window6B3SupportCount.supportZero.card =
      Omega.GU.Window6C3SupportCount.c3Support.card := by
  rw [Omega.GU.Window6B3SupportCount.supportZero_card, Omega.GU.Window6C3SupportCount.c3Support_card]

end Omega.GU
