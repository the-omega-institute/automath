import Mathlib.Data.Real.Basic

namespace Omega.SPG

/-- Paper-facing corollary: package the Gödel/volume identification and the Stokes/volume formula
into one transitive dimension chain.
cor:spg-stokes-godel-dimension-chain -/
theorem paper_spg_stokes_godel_dimension_chain
    (n dG dV stokesDim : Real) (hGV : dG = dV) (hStokes : dV = n + stokesDim) :
    dG = dV ∧ dV = n + stokesDim ∧ dG = n + stokesDim := by
  refine ⟨hGV, hStokes, ?_⟩
  calc
    dG = dV := hGV
    _ = n + stokesDim := hStokes

end Omega.SPG
