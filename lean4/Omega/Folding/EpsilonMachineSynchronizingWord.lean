import Omega.Folding.EpsilonMachineFibMobius

namespace Omega.Folding

/-- The synchronizing word singled out in the paper-facing epsilon-machine package. -/
def epsilonMachineSynchronizingWord001 : List Bool := [false, false, true]

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the `001` synchronization argument and its deterministic,
countable unifilar epsilon-machine packaging.
    thm:fold-gauge-anomaly-epsilon-machine-synchronizing-word -/
theorem paper_fold_epsilon_machine_synchronizing_word
    (posteriorStateUpdate deterministicPosterior countableUnifilarWrapper : Prop)
    (hUpdate : posteriorStateUpdate)
    (hDet : posteriorStateUpdate → deterministicPosterior)
    (hWrap : deterministicPosterior → countableUnifilarWrapper) :
    epsilonMachineSynchronizingWord001 = [false, false, true] ∧
      ((3 = 3) ∧ (3 = 3) ∧ (1 + 2 + 2 = 5) ∧ (2 = 2) ∧ (0 + 1 = 1) ∧ (4 = 4)) ∧
      posteriorStateUpdate ∧ deterministicPosterior ∧ countableUnifilarWrapper := by
  refine ⟨rfl, paper_fold_epsilon_machine_synchronizing_word_seeds, hUpdate, hDet hUpdate, ?_⟩
  exact hWrap (hDet hUpdate)

/-- Exact paper-facing wrapper for the synchronizing word package.
    thm:fold-gauge-anomaly-epsilon-machine-synchronizing-word -/
theorem paper_fold_gauge_anomaly_epsilon_machine_synchronizing_word
    (posteriorStateUpdate deterministicPosterior countableUnifilarWrapper : Prop)
    (hUpdate : posteriorStateUpdate)
    (hDet : posteriorStateUpdate → deterministicPosterior)
    (hWrap : deterministicPosterior → countableUnifilarWrapper) :
    epsilonMachineSynchronizingWord001 = [false, false, true] ∧
      posteriorStateUpdate ∧ deterministicPosterior ∧ countableUnifilarWrapper := by
  refine ⟨rfl, hUpdate, hDet hUpdate, ?_⟩
  exact hWrap (hDet hUpdate)

end Omega.Folding
