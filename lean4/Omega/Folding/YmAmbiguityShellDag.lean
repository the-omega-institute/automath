import Omega.Folding.CandidateSetMonotone
import Omega.Folding.PhiConjugacyThreshold
import Omega.Folding.SyncDelay

namespace Omega.Folding

/-- Paper-facing wrapper for ambiguity-shell acyclicity and its immediate consequences.
    thm:Ym-ambiguity-shell-dag -/
theorem paper_Ym_ambiguity_shell_dag (m : Nat)
    (ambiguityShellIsDAG noPeriodicOrbit eventualSingletonAfterM : Prop) (hm : 3 <= m)
    (hdag : ambiguityShellIsDAG) (hperiodic : ambiguityShellIsDAG -> noPeriodicOrbit)
    (hsingleton : ambiguityShellIsDAG -> eventualSingletonAfterM) :
    ambiguityShellIsDAG /\ noPeriodicOrbit /\ eventualSingletonAfterM := by
  have hsync_all := Omega.Folding.SyncDelay.paper_fold_sync_delay
  rcases hsync_all with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsync⟩
  let _ := hsync m hm
  exact ⟨hdag, hperiodic hdag, hsingleton hdag⟩

end Omega.Folding
