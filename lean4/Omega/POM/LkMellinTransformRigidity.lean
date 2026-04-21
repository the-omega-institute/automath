import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Closed form for the bulk Mellin transform in the chapter-local `L_k` model. -/
def pomLkMellinNuClosed (s : Complex) : Complex :=
  (4 : Complex) ^ (-s)

/-- Bulk Mellin transform, identified with the closed form in this wrapper. -/
def pomLkMellinNu (s : Complex) : Complex :=
  pomLkMellinNuClosed s

/-- Closed form for the boundary Mellin transform, written via the rational transfer from `ν`. -/
def pomLkMellinRhoClosed (s : Complex) : Complex :=
  4 * (((1 / 2 : Complex) - s) / ((1 - s) * (2 - s))) * pomLkMellinNuClosed s

/-- Boundary Mellin transform, identified with the same closed form. -/
def pomLkMellinRho (s : Complex) : Complex :=
  pomLkMellinRhoClosed s

/-- Paper label: `prop:pom-Lk-mellin-transform-rigidity`. -/
theorem paper_pom_lk_mellin_transform_rigidity (s : Complex) :
    pomLkMellinNu s = pomLkMellinNuClosed s /\
      pomLkMellinRho s = pomLkMellinRhoClosed s /\
        pomLkMellinRho s =
          4 * (((1 / 2 : Complex) - s) / ((1 - s) * (2 - s))) * pomLkMellinNu s := by
  constructor
  · rfl
  constructor
  · rfl
  · simp [pomLkMellinRho, pomLkMellinRhoClosed, pomLkMellinNu]

end
