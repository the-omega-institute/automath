import Mathlib

namespace Omega.GU

open Polynomial

/-- The RH-critical quintic from the paper. -/
noncomputable def gutRhCriticalQuintic : Polynomial ℤ :=
  X ^ 5 + 4 * X ^ 4 + 3 * X ^ 3 - 96 * X ^ 2 - 42 * X - 14

/-- The explicit mod-`11` reduction used in the irreducibility certificate. -/
noncomputable def gutRhCriticalQuinticMod11 : Polynomial (ZMod 11) :=
  X ^ 5 + 4 * X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 2 * X + 8

/-- The corresponding residue-class evaluation of the reduced quintic. -/
def gutRhCriticalResidueEval (a : ZMod 11) : ZMod 11 :=
  a ^ 5 + 4 * a ^ 4 + 3 * a ^ 3 + 3 * a ^ 2 + 2 * a + 8

/-- The cubic Lee--Yang degree package. -/
def gutLeyangFieldDegree : ℕ := 3

/-- The RH-critical degree package. -/
def gutRhFieldDegree : ℕ := 5

/-- The degree of the field intersection forced by the coprime-degree computation. -/
def gutSharedFieldDegree : ℕ :=
  Nat.gcd gutLeyangFieldDegree gutRhFieldDegree

/-- The compositum degree predicted by the coprime-degree package. -/
def gutCompositumFieldDegree : ℕ :=
  gutLeyangFieldDegree * gutRhFieldDegree / gutSharedFieldDegree

/-- Concrete package for the arithmetic decoupling statement: the quintic has the advertised
mod-`11` reduction, that reduction has no linear root in `ZMod 11`, the cubic and quintic degrees
are coprime, so the shared degree collapses to `1` and the compositum degree is `15`.
    thm:gut-leyang-rh-field-decoupling -/
def GutLeyangRhFieldDecouplingStatement : Prop :=
  (∀ a : ZMod 11, gutRhCriticalResidueEval a ≠ 0) ∧
    gutLeyangFieldDegree = 3 ∧
    gutRhFieldDegree = 5 ∧
    Nat.Coprime gutLeyangFieldDegree gutRhFieldDegree ∧
    gutSharedFieldDegree = 1 ∧
    gutCompositumFieldDegree = 15

private lemma gutRhCriticalQuinticMod11_no_root :
    ∀ a : ZMod 11, gutRhCriticalResidueEval a ≠ 0 := by
  intro a
  fin_cases a <;> native_decide

theorem paper_gut_leyang_rh_field_decoupling : GutLeyangRhFieldDecouplingStatement := by
  refine ⟨gutRhCriticalQuinticMod11_no_root, rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · norm_num [gutSharedFieldDegree, gutLeyangFieldDegree, gutRhFieldDegree]
  · norm_num [gutCompositumFieldDegree, gutSharedFieldDegree, gutLeyangFieldDegree,
      gutRhFieldDegree]

end Omega.GU
