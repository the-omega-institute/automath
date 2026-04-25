import Omega.Zeta.Conclusion62MellinRational
import Omega.Zeta.FiniteRhPhaseLift

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-dyadic-flux-finite-state-vertical-pole-grids`.
The existing finite-state Mellin rationality package identifies the determinant controlling the
possible poles, and the cyclic phase-lift package organizes those poles into explicit vertical
arithmetic grids. -/
theorem paper_conclusion_dyadic_flux_finite_state_vertical_pole_grids
    (d : ℕ) (w a : Fin d → ℂ) (D : FiniteRhPhaseLiftData) :
    (∀ s, Matrix.det (conclusion62SystemMatrix a s) = conclusion62PolePolynomial a s) ∧
      D.phaseRefinement ∧
      D.spectralRadiusPreserved ∧
      D.ramanujanBoundPreserved ∧
      D.criticalLineCombRefinement := by
  rcases paper_conclusion62_mellin_rational d w a with ⟨_, hdet, _⟩
  rcases paper_finite_rh_phase_lift D with ⟨hphase, hspec, hram, hcomb⟩
  exact ⟨hdet, hphase, hspec, hram, hcomb⟩

end Omega.Conclusion
