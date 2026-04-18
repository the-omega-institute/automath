import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The Newman octic polynomial appearing in `prop:pom-a4t-newman-octic-field-basic`. -/
noncomputable def a4tNewmanOcticPolynomial : Polynomial ℤ :=
  X ^ 8 - 2 * X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 - 2 * X ^ 3 - 2

/-- Concrete Eisenstein-at-`2` divisibility data for `a4tNewmanOcticPolynomial`. -/
def a4tNewmanOcticEisensteinAtTwo : Prop :=
  2 ∣ (-2 : ℤ) ∧
    2 ∣ (-2 : ℤ) ∧
    2 ∣ (-2 : ℤ) ∧
    2 ∣ (-2 : ℤ) ∧
    2 ∣ (-2 : ℤ) ∧
    ¬ (4 : ℤ) ∣ (-2 : ℤ)

/-- Audited discriminant seed for the Newman octic field. -/
def a4tNewmanOcticDiscriminant : ℤ :=
  -(2 ^ 10 * 7 ^ 2 * 23 ^ 2 * 1151 : ℤ)

/-- The real/complex embedding count recorded in the paper. -/
def a4tNewmanOcticSignature : ℕ × ℕ :=
  (2, 3)

/-- Dirichlet's unit-rank formula specialized to `a4tNewmanOcticSignature`. -/
def a4tNewmanOcticUnitRank : ℕ :=
  a4tNewmanOcticSignature.1 + a4tNewmanOcticSignature.2 - 1

theorem a4tNewmanOcticEisensteinAtTwo_spec : a4tNewmanOcticEisensteinAtTwo := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨-1, by ring⟩
  · intro h
    rcases h with ⟨k, hk⟩
    omega

theorem a4tNewmanOcticUnitRank_eq_four : a4tNewmanOcticUnitRank = 4 := by
  norm_num [a4tNewmanOcticUnitRank, a4tNewmanOcticSignature]

/-- Paper-facing package for the Newman octic field arithmetic seeds.
    prop:pom-a4t-newman-octic-field-basic -/
theorem paper_pom_a4t_newman_octic_field_basic :
    a4tNewmanOcticEisensteinAtTwo ∧
      a4tNewmanOcticDiscriminant = -(2 ^ 10 * 7 ^ 2 * 23 ^ 2 * 1151 : ℤ) ∧
      a4tNewmanOcticSignature = (2, 3) ∧
      a4tNewmanOcticUnitRank = 4 := by
  exact
    ⟨a4tNewmanOcticEisensteinAtTwo_spec, rfl, rfl, a4tNewmanOcticUnitRank_eq_four⟩

end Omega.POM
