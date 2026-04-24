import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryParityNotMeasurableFromF8
import Omega.GroupUnification.Window6F8RepairBitNoBoundaryCovariantExtension

namespace Omega.GroupUnification

open Omega.Conclusion

/-- The `F₈` repair-bit hidden channel restricted to the boundary sector. -/
abbrev f8RepairBitChannel : Window6BoundaryPoint → Bool :=
  window6F8RepairBit

/-- The canonical boundary parity channel on the same boundary sector. -/
abbrev canonicalBoundaryParityChannel : Window6BoundaryPoint → Bool :=
  window6CanonicalBoundaryParity

/-- The `F₈` repair bit and the canonical `F₉` boundary parity cannot be the same boundary
channel: the former is constantly `false`, while the latter flips with the boundary sheet.
    cor:window6-f8-repair-vs-f9-boundary-parity-separated -/
theorem paper_window6_f8_repair_vs_f9_boundary_parity_separated :
    f8RepairBitChannel ≠ canonicalBoundaryParityChannel := by
  intro hEq
  have hconst := paper_window6_f8_repair_bit_no_boundary_covariant_extension.1
  have hparity :
      canonicalBoundaryParityChannel ((0 : Fin 3), true) = false := by
    simpa [f8RepairBitChannel, canonicalBoundaryParityChannel, hEq] using
      hconst ((0 : Fin 3), true)
  simp [canonicalBoundaryParityChannel, window6CanonicalBoundaryParity] at hparity

end Omega.GroupUnification
