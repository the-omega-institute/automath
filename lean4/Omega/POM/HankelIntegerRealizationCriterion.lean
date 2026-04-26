import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.POM.HankelSmithMinimalDenominator

namespace Omega.POM

open scoped BigOperators

/-- Concrete Smith data for the integral-realization test. -/
structure pom_hankel_integer_realization_criterion_data where
  d : Nat
  smith : pom_hankel_smith_minimal_denominator_data d
  smithDiagonal_pos : ∀ i : Fin d, 0 < smith.smithDiagonal i

/-- The minimal common denominator inherited from the Smith package. -/
noncomputable def pom_hankel_integer_realization_criterion_minimal_denominator
    (D : pom_hankel_integer_realization_criterion_data) : Nat :=
  pom_hankel_smith_minimal_denominator_lcm D.smith

/-- Rowwise clearing factor `s_i / gcd(s_i,g_i)`. -/
def pom_hankel_integer_realization_criterion_row_factor
    (D : pom_hankel_integer_realization_criterion_data) (i : Fin D.d) : Nat :=
  pom_hankel_smith_minimal_denominator_row_factor D.smith i

/-- The integer-realization predicate: no denominator is needed. -/
noncomputable def pom_hankel_integer_realization_criterion_integer_realization
    (D : pom_hankel_integer_realization_criterion_data) : Prop :=
  pom_hankel_integer_realization_criterion_minimal_denominator D = 1

/-- The row gcd divisibility condition `s_i ∣ g_i`. -/
def pom_hankel_integer_realization_criterion_row_gcd_divisibility
    (D : pom_hankel_integer_realization_criterion_data) : Prop :=
  ∀ i : Fin D.d, D.smith.smithDiagonal i ∣ D.smith.rowGcd i

/-- The prime-valuation criterion for the minimal denominator. -/
noncomputable def pom_hankel_integer_realization_criterion_prime_valuation_zero
    (D : pom_hankel_integer_realization_criterion_data) : Prop :=
  ∀ p : Nat,
    Nat.Prime p →
      (pom_hankel_integer_realization_criterion_minimal_denominator D).factorization p = 0

lemma pom_hankel_integer_realization_criterion_row_factor_eq_one_iff
    (D : pom_hankel_integer_realization_criterion_data) (i : Fin D.d) :
    pom_hankel_integer_realization_criterion_row_factor D i = 1 ↔
      D.smith.smithDiagonal i ∣ D.smith.rowGcd i := by
  constructor
  · intro h
    have hdiv :
        D.smith.smithDiagonal i / Nat.gcd (D.smith.smithDiagonal i) (D.smith.rowGcd i) = 1 := by
      simpa [pom_hankel_integer_realization_criterion_row_factor,
        pom_hankel_smith_minimal_denominator_row_factor] using h
    have hgcd_eq :
        Nat.gcd (D.smith.smithDiagonal i) (D.smith.rowGcd i) = D.smith.smithDiagonal i :=
      Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_left _ _) hdiv
    simpa [hgcd_eq] using Nat.gcd_dvd_right (D.smith.smithDiagonal i) (D.smith.rowGcd i)
  · intro h
    have hgcd :
        Nat.gcd (D.smith.smithDiagonal i) (D.smith.rowGcd i) = D.smith.smithDiagonal i :=
      Nat.gcd_eq_left h
    simp [pom_hankel_integer_realization_criterion_row_factor,
      pom_hankel_smith_minimal_denominator_row_factor, hgcd, D.smithDiagonal_pos i]

/-- Paper-facing equivalence of integrality, denominator one, row divisibility, and prime
valuation vanishing. -/
noncomputable def pom_hankel_integer_realization_criterion_statement
    (D : pom_hankel_integer_realization_criterion_data) : Prop :=
  pom_hankel_integer_realization_criterion_integer_realization D ↔
    pom_hankel_integer_realization_criterion_minimal_denominator D = 1 ∧
      pom_hankel_integer_realization_criterion_row_gcd_divisibility D ∧
      pom_hankel_integer_realization_criterion_prime_valuation_zero D

/-- Paper label: `cor:pom-hankel-integer-realization-criterion`. -/
theorem paper_pom_hankel_integer_realization_criterion
    (D : pom_hankel_integer_realization_criterion_data) :
    pom_hankel_integer_realization_criterion_statement D := by
  constructor
  · intro hN
    refine ⟨hN, ?_, ?_⟩
    · intro i
      rw [← pom_hankel_integer_realization_criterion_row_factor_eq_one_iff D i]
      apply Nat.dvd_one.mp
      rw [← hN]
      exact Finset.dvd_lcm (Finset.mem_univ i)
    · intro p hp
      have hN' :
          pom_hankel_integer_realization_criterion_minimal_denominator D = 1 := by
        simpa [pom_hankel_integer_realization_criterion_integer_realization] using hN
      simp [hN']
  · intro h
    exact h.1

end Omega.POM
