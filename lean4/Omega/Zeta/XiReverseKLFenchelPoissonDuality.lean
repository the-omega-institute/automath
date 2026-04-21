import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing wrapper for the Fenchel--Poisson duality package for reverse-KL.
    thm:xi-reversekl-fenchel-poisson-duality -/
theorem paper_xi_reversekl_fenchel_poisson_duality (dualFormula optimizerStatement : Prop)
    (hDual : dualFormula) (hOpt : optimizerStatement) : dualFormula ∧ optimizerStatement := by
  exact ⟨hDual, hOpt⟩

end Omega.Zeta
