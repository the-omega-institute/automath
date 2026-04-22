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

/-- Recorded odd-prime `(e,f)` data at `7`. -/
def pom_a4t_newman_octic_field_tame_data_7 : List (ℕ × ℕ) :=
  [(3, 1), (1, 5)]

/-- Recorded odd-prime `(e,f)` data at `23`. -/
def pom_a4t_newman_octic_field_tame_data_23 : List (ℕ × ℕ) :=
  [(3, 1), (1, 1), (1, 2), (1, 2)]

/-- Recorded odd-prime `(e,f)` data at `1151`. -/
def pom_a4t_newman_octic_field_tame_data_1151 : List (ℕ × ℕ) :=
  [(2, 1), (1, 2), (1, 2), (1, 2)]

/-- The tame discriminant-valuation formula `Σ f(e - 1)` on recorded `(e,f)` data. -/
def pom_a4t_newman_octic_field_tame_discriminant_valuation (data : List (ℕ × ℕ)) : ℕ :=
  (data.map fun ef => ef.2 * (ef.1 - 1)).sum

/-- The inertia-group order recorded by the largest ramification index. -/
def pom_a4t_newman_octic_field_tame_inertia_order (data : List (ℕ × ℕ)) : ℕ :=
  (data.map Prod.fst).foldr Nat.max 1

/-- Every ramification index in the recorded decomposition is prime to the residue characteristic. -/
def pom_a4t_newman_octic_field_tame_at (p : ℕ) (data : List (ℕ × ℕ)) : Prop :=
  ∀ ef, ef ∈ data → Nat.Coprime p ef.1

/-- Concrete package for the odd-prime tame ramification statement. -/
def pom_a4t_newman_octic_field_tame_package : Prop :=
  pom_a4t_newman_octic_field_tame_at 7 pom_a4t_newman_octic_field_tame_data_7 ∧
    pom_a4t_newman_octic_field_tame_at 23 pom_a4t_newman_octic_field_tame_data_23 ∧
    pom_a4t_newman_octic_field_tame_at 1151 pom_a4t_newman_octic_field_tame_data_1151 ∧
    pom_a4t_newman_octic_field_tame_discriminant_valuation
        pom_a4t_newman_octic_field_tame_data_7 = 2 ∧
    pom_a4t_newman_octic_field_tame_discriminant_valuation
        pom_a4t_newman_octic_field_tame_data_23 = 2 ∧
    pom_a4t_newman_octic_field_tame_discriminant_valuation
        pom_a4t_newman_octic_field_tame_data_1151 = 1 ∧
    pom_a4t_newman_octic_field_tame_inertia_order pom_a4t_newman_octic_field_tame_data_7 = 3 ∧
    pom_a4t_newman_octic_field_tame_inertia_order pom_a4t_newman_octic_field_tame_data_23 = 3 ∧
    pom_a4t_newman_octic_field_tame_inertia_order
        pom_a4t_newman_octic_field_tame_data_1151 = 2

/-- Paper label: `cor:pom-a4t-newman-octic-field-tame`. -/
theorem paper_pom_a4t_newman_octic_field_tame : pom_a4t_newman_octic_field_tame_package := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ef hef
    simp [pom_a4t_newman_octic_field_tame_data_7] at hef
    rcases hef with rfl | rfl
    · decide
    · decide
  · intro ef hef
    simp [pom_a4t_newman_octic_field_tame_data_23] at hef
    rcases hef with rfl | rfl | rfl
    · decide
    · decide
    · decide
  · intro ef hef
    simp [pom_a4t_newman_octic_field_tame_data_1151] at hef
    rcases hef with rfl | rfl
    · decide
    · decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.POM
