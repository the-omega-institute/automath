import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40AtomicWittDirichletComb
import Omega.SyncKernelWeighted.RealInput40LogMSplit
import Omega.SyncKernelWeighted.RealInput40PrimeArtinSplitting

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `prop:atomic-2-orbit-split-logM`. The real-input-`40` primitive package isolates
the unique atomic Witt pulse at length `2`; the primitive-orbit split identifies the matching
two-step half-orbit correction; and the finite-part package rewrites the exact logarithmic
correction as `logMM - logMIn = pVertAtPole`. -/
theorem paper_atomic_2_orbit_split_logM
    (D : RealInput40LogMSplitData) (A : RealInput40AtomicWittDirichletCombData) (u v : ℤ) :
    A.atomicPrimitive 2 = A.u ∧
      realInput40PrimeArtinOrbitCount u v 2 = realInput40ArtinTrace u v 2 + (u + v) ∧
      D.logMM - D.logMIn = D.pVertAtPole := by
  refine ⟨(paper_killo_real_input_40_atomic_witt_dirichlet_comb A).2.1.1, ?_, ?_⟩
  · simpa using paper_real_input_40_prime_artin_splitting u v 2
  · calc
      D.logMM - D.logMIn = (D.logMIn + D.pVertAtPole) - D.logMIn := by
        rw [paper_real_input_40_logM_split]
      _ = D.pVertAtPole := by ring

end

end Omega.SyncKernelWeighted
