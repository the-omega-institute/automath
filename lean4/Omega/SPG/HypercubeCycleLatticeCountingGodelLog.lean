import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.HypercubeCycleLatticeGodelEllipsoidCounting

namespace Omega.SPG

noncomputable section

/-- Paper label: `cor:hypercube-cycle-lattice-counting-godel-log`. The already-packaged
cycle-lattice ellipsoid main term gives the logarithmic counting law, and any external Gödel
encoding may be carried along as an injective readout witness. -/
theorem paper_hypercube_cycle_lattice_counting_godel_log
    (rank treeCount : ℕ) (unitBallVolume radius : ℝ)
    (encoding : ℕ → ℕ) (hencoding : Function.Injective encoding)
    (hball : 0 < unitBallVolume) (htree : 0 < treeCount) (hR : 0 < radius) :
    hypercubeCycleLatticeGodelCountMainTerm rank 1 treeCount unitBallVolume radius =
      unitBallVolume * radius ^ rank / Real.sqrt treeCount ∧
      Function.Injective encoding ∧
      Real.log (hypercubeCycleLatticeGodelCountMainTerm rank 1 treeCount unitBallVolume radius) =
        Real.log unitBallVolume - (1 / 2 : ℝ) * Real.log treeCount + (rank : ℝ) * Real.log radius := by
  rcases paper_hypercube_cycle_lattice_godel_ellipsoid_counting
      rank 1 treeCount unitBallVolume radius hball (by norm_num) htree hR with
    ⟨_, hcount, hlog⟩
  refine ⟨?_, hencoding, ?_⟩
  · simpa using hcount
  · simpa using hlog

end

end Omega.SPG
