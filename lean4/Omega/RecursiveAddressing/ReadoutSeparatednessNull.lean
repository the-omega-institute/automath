import Mathlib.Tactic

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing core for the separatedness criterion at a stable address:
    uniqueness of a section from all finite dyadic restrictions is exactly injectivity of the
    restriction tuple map.
    thm:recursive-addressing-readout-separatedness-null -/
theorem paper_recursive_addressing_readout_separatedness_null
    {Section Piece : Type*} {ι : Type*} (restrict : ι → Section → Piece) :
    (∀ s t : Section, (∀ i : ι, restrict i s = restrict i t) → s = t) ↔
      Function.Injective (fun s : Section => fun i : ι => restrict i s) := by
  constructor
  · intro h s t hEq
    exact h s t (fun i => congrFun hEq i)
  · intro hinj s t hEq
    exact hinj (funext hEq)

end Omega.RecursiveAddressing
