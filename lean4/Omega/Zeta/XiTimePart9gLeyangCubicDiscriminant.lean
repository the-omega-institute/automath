import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The Lee-Yang cubic kernel from xi-time part `9g`. -/
def xiTimePart9gLeyangCubic (y : ℤ) : ℤ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The cubic discriminant formula in coefficient form for the xi-time part `9g` Lee-Yang cubic. -/
def xiTimePart9gCubicDiscriminantFormula (a b c d : ℤ) : ℤ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The discriminant of `256 y^3 + 411 y^2 + 165 y + 32`. -/
def xiTimePart9gLeyangCubicDiscriminant : ℤ :=
  xiTimePart9gCubicDiscriminantFormula 256 411 165 32

/-- The mod-`5` reduction `y^3 + y^2 + 2` of the Lee-Yang cubic kernel. -/
def xiTimePart9gLeyangCubicMod5 (y : ZMod 5) : ZMod 5 :=
  y ^ 3 + y ^ 2 + 2

/-- The mod-`5` reduction has no root, hence the cubic is irreducible over `ℚ`. -/
def xiTimePart9gLeyangCubicMod5Irreducible : Prop :=
  ∀ y : ZMod 5, xiTimePart9gLeyangCubicMod5 y ≠ 0

private theorem xiTimePart9gLeyangCubicDiscriminant_eval :
    xiTimePart9gLeyangCubicDiscriminant = -((3 : ℤ) ^ 9 * 31 ^ 2 * 37) := by
  norm_num [xiTimePart9gLeyangCubicDiscriminant, xiTimePart9gCubicDiscriminantFormula]

private theorem xiTimePart9gLeyangCubicMod5Irreducible_true :
    xiTimePart9gLeyangCubicMod5Irreducible := by
  intro y
  fin_cases y <;> decide

private theorem xiTimePart9gLeyangCubicDiscriminant_not_square :
    ¬ IsSquare xiTimePart9gLeyangCubicDiscriminant := by
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have hnonneg : 0 ≤ xiTimePart9gLeyangCubicDiscriminant := by
    simpa [pow_two, hn] using sq_nonneg n
  rw [xiTimePart9gLeyangCubicDiscriminant_eval] at hnonneg
  norm_num at hnonneg

/-- The Lee-Yang cubic kernel has the displayed discriminant, is irreducible modulo `5`, and that
discriminant is not a square, providing the local `S₃` audit certificate.
    thm:xi-time-part9g-leyang-cubic-discriminant -/
theorem paper_xi_time_part9g_leyang_cubic_discriminant :
    xiTimePart9gLeyangCubicDiscriminant = -((3 : ℤ) ^ 9 * 31 ^ 2 * 37) ∧
      xiTimePart9gLeyangCubicMod5Irreducible ∧
      ¬ IsSquare xiTimePart9gLeyangCubicDiscriminant := by
  exact ⟨xiTimePart9gLeyangCubicDiscriminant_eval, xiTimePart9gLeyangCubicMod5Irreducible_true,
    xiTimePart9gLeyangCubicDiscriminant_not_square⟩

end Omega.Zeta
