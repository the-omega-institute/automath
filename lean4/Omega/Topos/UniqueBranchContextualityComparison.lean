namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the discrete-stack part of the unique-branch
contextuality comparison.
    thm:unique-branch-contextuality-comparison -/
theorem paper_gluing_failure_unique_branch_contextuality_comparison
    {State Ref : Type}
    (CompSec Sec NullGlue : State → Ref → Prop)
    (compatibleFamily globalSection : Prop)
    {p : State} {r : Ref}
    (hComp : CompSec p r ↔ compatibleFamily)
    (hSec : Sec p r ↔ globalSection)
    (hNull : NullGlue p r ↔ CompSec p r ∧ ¬ Sec p r) :
    (CompSec p r ↔ compatibleFamily) ∧
      (Sec p r ↔ globalSection) ∧
      (NullGlue p r ↔ compatibleFamily ∧ ¬ globalSection) := by
  refine ⟨hComp, hSec, ?_⟩
  constructor
  · intro hGlue
    rcases hNull.mp hGlue with ⟨hCompSec, hNotSec⟩
    refine ⟨hComp.mp hCompSec, ?_⟩
    intro hGlobal
    exact hNotSec (hSec.mpr hGlobal)
  · intro hContextual
    refine hNull.mpr ⟨hComp.mpr hContextual.1, ?_⟩
    intro hSec'
    exact hContextual.2 (hSec.mp hSec')

end Omega.Topos
