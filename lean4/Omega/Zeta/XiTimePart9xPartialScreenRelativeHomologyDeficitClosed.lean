import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9x-partial-screen-relative-homology-deficit-closed`. -/
theorem paper_xi_time_part9x_partial_screen_relative_homology_deficit_closed
    {Cₙ Obs : Type*} [Zero Obs] (fS : Cₙ → Obs)
    (relativeCycles relativeBoundaries relativeHomology : Set Cₙ)
    (kernelRank components : ℕ)
    (hker : {x | fS x = 0} = relativeCycles)
    (hboundaries : relativeBoundaries = (∅ : Set Cₙ))
    (hhomology : relativeHomology = relativeCycles \ relativeBoundaries)
    (hrank : kernelRank = components - 1) :
    {x | fS x = 0} = relativeHomology ∧ kernelRank = components - 1 := by
  constructor
  · rw [hker, hhomology, hboundaries]
    simp
  · exact hrank

end Omega.Zeta
