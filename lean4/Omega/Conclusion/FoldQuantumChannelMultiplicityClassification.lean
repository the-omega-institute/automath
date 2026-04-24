import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.Conclusion

/-- The fiber multiplicity multiset of the folded quantum channel is determined exactly by the
multiset of squared Choi block ranks. -/
theorem paper_conclusion_fold_quantum_channel_multiplicity_classification
    (D D' : Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData) :
    List.Perm D.blockRanks D'.blockRanks ↔ List.Perm D.choiBlockRanks D'.choiBlockRanks := by
  have hsquare_injective : Function.Injective (fun d : ℕ => d ^ 2) := by
    intro a b hab
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hab
  constructor
  · intro hperm
    simpa [Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData.choiBlockRanks,
      Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData.fiberBlockRanks] using
      hperm.map (fun d => d ^ 2)
  · intro hperm
    have hmap :
        List.Perm (D.blockRanks.map fun d => d ^ 2) (D'.blockRanks.map fun d => d ^ 2) := by
      simpa [Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData.choiBlockRanks,
        Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData.fiberBlockRanks] using hperm
    exact
      (List.map_perm_map_iff (l := D.blockRanks) (l' := D'.blockRanks)
        (f := fun d => d ^ 2) hsquare_injective).mp hmap

end Omega.Conclusion
