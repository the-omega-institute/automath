import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedLeyangCubicModelsCommonQuadraticResolvent
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation
import Omega.Zeta.XiTimePart9gLeyangCubicDiscriminant

namespace Omega.DerivedConsequences

/-- The common cubic degree carried by the Lee--Yang invariants `u`, `b`, and `λ_*`. -/
def derived_leyang_cubic_invariants_no_quadratic_radicals_common_field_degree : ℕ := 3

/-- The audited `S₃` Galois closure degree. -/
def derived_leyang_cubic_invariants_no_quadratic_radicals_galois_closure_degree : ℕ :=
  Nat.factorial 3

/-- Any tower built only from quadratic radicals has degree a power of `2`. -/
def derived_leyang_cubic_invariants_no_quadratic_radicals_quadratic_tower_degree (r : ℕ) : ℕ :=
  2 ^ r

private lemma derived_leyang_cubic_invariants_no_quadratic_radicals_three_not_dvd_two_pow
    (r : ℕ) : ¬ 3 ∣ 2 ^ r := by
  intro h
  have hthree : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow h
  omega

/-- Concrete Lee--Yang cubic package: both audited cubic models carry the existing `S₃` data and
common quadratic resolvent `-111`, all three invariant fields have degree `3`, the Galois closure
has degree `6`, so the cubic field is not Galois and cannot lie in any quadratic-radical tower
because `3 ∤ 2^r`. -/
def derived_leyang_cubic_invariants_no_quadratic_radicals_statement : Prop :=
  Omega.Zeta.xiTerminalKappaSquareS3Audit ∧
    Omega.Zeta.xiTimePart9gLeyangCubicMod5Irreducible ∧
    ¬ IsSquare Omega.Zeta.xiTimePart9gLeyangCubicDiscriminant ∧
    Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
    derived_leyang_cubic_invariants_no_quadratic_radicals_common_field_degree = 3 ∧
    derived_leyang_cubic_invariants_no_quadratic_radicals_galois_closure_degree = 6 ∧
    derived_leyang_cubic_invariants_no_quadratic_radicals_common_field_degree <
      derived_leyang_cubic_invariants_no_quadratic_radicals_galois_closure_degree ∧
    ∀ r : ℕ,
      ¬ derived_leyang_cubic_invariants_no_quadratic_radicals_common_field_degree ∣
        derived_leyang_cubic_invariants_no_quadratic_radicals_quadratic_tower_degree r

/-- Paper label: `thm:derived-leyang-cubic-invariants-no-quadratic-radicals`. -/
def paper_derived_leyang_cubic_invariants_no_quadratic_radicals : Prop := by
  exact derived_leyang_cubic_invariants_no_quadratic_radicals_statement

end Omega.DerivedConsequences
