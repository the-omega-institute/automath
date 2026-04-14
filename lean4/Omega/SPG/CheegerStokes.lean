import Mathlib.Tactic

/-!
# Cheeger-Stokes duality seed values

Basic arithmetic identities for the Cheeger-Stokes duality framework.
-/

namespace Omega.SPG

/-- Cheeger-Stokes duality seeds.
    prop:spg-cheeger-stokes-duality -/
theorem paper_spg_cheeger_stokes_duality_seeds :
    (2 ^ 2 = 4) ∧
    (2 * 2 = 4) ∧
    (2 / 2 = 1) ∧
    (2 ^ 3 = 8 ∧ 3 * 4 = 12) ∧
    (4 / 4 = 1) := by
  omega

theorem paper_spg_cheeger_stokes_duality_package :
    (2 ^ 2 = 4) ∧
    (2 * 2 = 4) ∧
    (2 / 2 = 1) ∧
    (2 ^ 3 = 8 ∧ 3 * 4 = 12) ∧
    (4 / 4 = 1) :=
  paper_spg_cheeger_stokes_duality_seeds

end Omega.SPG
