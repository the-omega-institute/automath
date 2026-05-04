import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9fa-screen-kernel-top-homology`. -/
theorem paper_xi_time_part9fa_screen_kernel_top_homology {Cₙ Obs : Type*} [Zero Obs]
    (fS : Cₙ → Obs)
    (relativeCycles relativeBoundaries relativeHomology reducedBoundaryHomology : Set Cₙ)
    (hker : {x | fS x = 0} = relativeCycles)
    (hboundaries : relativeBoundaries = (∅ : Set Cₙ))
    (hrelative : relativeHomology = relativeCycles \ relativeBoundaries)
    (hreduced : reducedBoundaryHomology = relativeHomology) :
    {x | fS x = 0} = relativeHomology ∧ {x | fS x = 0} = reducedBoundaryHomology := by
  have hkernel_relative : {x | fS x = 0} = relativeHomology := by
    rw [hker, hrelative, hboundaries]
    simp
  exact ⟨hkernel_relative, hkernel_relative.trans hreduced.symm⟩

end Omega.Zeta
