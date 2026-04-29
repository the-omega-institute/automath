import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70ad-hidden-logmultiplicity-exponential-moments`. -/
theorem paper_xi_time_part70ad_hidden_logmultiplicity_exponential_moments (p ell : Real) :
    let mean := -p * ell
    let centered2 := (1 - p) * (0 - mean) ^ 2 + p * (-ell - mean) ^ 2
    let centered3 := (1 - p) * (0 - mean) ^ 3 + p * (-ell - mean) ^ 3
    let centered4 := (1 - p) * (0 - mean) ^ 4 + p * (-ell - mean) ^ 4
    centered2 = p * (1 - p) * ell ^ 2 ∧
      centered3 = -p * (1 - p) * (1 - 2 * p) * ell ^ 3 ∧
        centered4 - 3 * centered2 ^ 2 =
          p * (1 - p) * (1 - 6 * p + 6 * p ^ 2) * ell ^ 4 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · ring
  · ring
  · ring_nf

end Omega.Zeta
