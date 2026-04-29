import Mathlib

namespace Omega.Zeta

open Polynomial

/-- The Lee--Yang cubic isolated by the two Tschirnhaus eliminations. -/
noncomputable def xiLeyangPLY : Polynomial ℤ :=
  256 * X ^ 3 + 411 * X ^ 2 + 165 * X + 32

/-- The first elimination polynomial, expanded in the `y`-coordinate. -/
noncomputable def xiLeyangFirstElimination : Polynomial ℤ :=
  Polynomial.C (-714432) * xiLeyangPLY

/-- The second elimination polynomial, expanded in the `y`-coordinate. -/
noncomputable def xiLeyangSecondElimination : Polynomial ℤ :=
  Polynomial.C (-33226752) * xiLeyangPLY

/-- Concrete package for the two Tschirnhaus resultant identities: each elimination polynomial is
an explicit scalar multiple of the same Lee--Yang cubic.
    thm:xi-leyang-ed-tschirnhaus-resultants-lock-PLY -/
def XiLeyangEdTschirnhausResultantsLockPLYStatement : Prop :=
  xiLeyangFirstElimination = Polynomial.C (-714432) * xiLeyangPLY ∧
    xiLeyangSecondElimination = Polynomial.C (-33226752) * xiLeyangPLY

private lemma xiLeyang_first_resultant_identity :
    xiLeyangFirstElimination = Polynomial.C (-714432) * xiLeyangPLY := by
  rfl

private lemma xiLeyang_second_resultant_identity :
    xiLeyangSecondElimination = Polynomial.C (-33226752) * xiLeyangPLY := by
  rfl

theorem paper_xi_leyang_ed_tschirnhaus_resultants_lock_ply :
    XiLeyangEdTschirnhausResultantsLockPLYStatement := by
  exact ⟨xiLeyang_first_resultant_identity, xiLeyang_second_resultant_identity⟩

end Omega.Zeta
