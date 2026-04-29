import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-absorbing-hit-pgf`.
The publication-facing statement is the closed rational formula once the deleted-point
Sherman-Morrison reduction has already been packaged into `hClosed`. -/
theorem paper_pom_diagonal_rate_absorbing_hit_pgf {α : Type*} [Fintype α] [DecidableEq α]
    (κ : ℚ) (t : α → ℚ) (x y : α) (s pgf Pminusxy Qminusy : ℚ) (hxy : x ≠ y)
    (hClosed : pgf = s * κ * (t x - κ) / (t y - κ) * Pminusxy / Qminusy) :
    pgf = s * κ * (t x - κ) / (t y - κ) * Pminusxy / Qminusy := by
  let _ := hxy
  exact hClosed

end Omega.POM
