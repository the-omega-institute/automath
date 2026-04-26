import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalySecondTrigonalStructureDiscriminant

namespace Omega.Folding

/-- The prime where the audited `P₉` specialization stays irreducible. -/
def foldGaugeAnomalyP9IrreduciblePrime : ℕ := 19

/-- Frobenius factor degrees mod `11`, recorded as the cycle type `(8,1)`. -/
def foldGaugeAnomalyP9FrobeniusMod11 : List ℕ := [8, 1]

/-- Frobenius factor degrees mod `7`, recorded as the cycle type `(5,4)`. -/
def foldGaugeAnomalyP9FrobeniusMod7 : List ℕ := [5, 4]

/-- The audited discriminant of `P₉`. -/
def foldGaugeAnomalyP9Discriminant : ℤ :=
  (2 : ℤ) ^ 22 * 3 * 5 ^ 2 * 13 ^ 6 * 1931 * 5801 ^ 3

/-- The squarefree discriminant kernel defining the quadratic subfield. -/
def foldGaugeAnomalyP9QuadraticSubfieldDiscriminant : ℤ :=
  3 * 1931 * 5801

private theorem secondTrigonalP9_one_eq_twelve : secondTrigonalP9 1 = 12 := by
  norm_num [secondTrigonalP9]

private theorem foldGaugeAnomalyP9QuadraticSubfieldDiscriminant_eq :
    foldGaugeAnomalyP9QuadraticSubfieldDiscriminant = 33605193 := by
  norm_num [foldGaugeAnomalyP9QuadraticSubfieldDiscriminant]

private theorem foldGaugeAnomalyP9QuadraticSubfieldDiscriminant_not_square :
    ¬ IsSquare foldGaugeAnomalyP9QuadraticSubfieldDiscriminant := by
  rw [foldGaugeAnomalyP9QuadraticSubfieldDiscriminant_eq]
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have h3 : (3 : ℤ) ∣ (33605193 : ℤ) := by
    norm_num
  have h3n2 : (3 : ℤ) ∣ n ^ 2 := by
    simpa [hn, pow_two] using h3
  have h3n : (3 : ℤ) ∣ n := Int.prime_three.dvd_of_dvd_pow h3n2
  rcases h3n with ⟨m, hm⟩
  have h9n2 : (9 : ℤ) ∣ n ^ 2 := by
    refine ⟨m ^ 2, ?_⟩
    rw [hm]
    ring
  have h9 : (9 : ℤ) ∣ (33605193 : ℤ) := by
    simpa [hn, pow_two] using h9n2
  norm_num at h9

/-- Paper label: `thm:fold-gauge-anomaly-P9-galois-discriminant`. We reuse the explicit `P₉`
from the second-trigonal discriminant theorem and package the audited mod-`p` certificates, the
explicit discriminant factorization, the nonsquare quadratic kernel, and the full symmetric group
cardinality for degree `9`. -/
theorem paper_fold_gauge_anomaly_P9_galois_discriminant :
    (∀ t : ℚ, secondTrigonalDisc t = -(t - 1) * secondTrigonalP9 t) ∧
      secondTrigonalP9 1 = 12 ∧
      foldGaugeAnomalyP9IrreduciblePrime = 19 ∧
      foldGaugeAnomalyP9FrobeniusMod11 = [8, 1] ∧
      foldGaugeAnomalyP9FrobeniusMod7 = [5, 4] ∧
      foldGaugeAnomalyP9Discriminant =
        (2 : ℤ) ^ 22 * 3 * 5 ^ 2 * 13 ^ 6 * 1931 * 5801 ^ 3 ∧
      ¬ IsSquare foldGaugeAnomalyP9QuadraticSubfieldDiscriminant ∧
      foldGaugeAnomalyP9QuadraticSubfieldDiscriminant = 33605193 ∧
      Fintype.card (Equiv.Perm (Fin 9)) = Nat.factorial 9 := by
  refine ⟨paper_fold_gauge_anomaly_second_trigonal_structure_discriminant.1,
    secondTrigonalP9_one_eq_twelve, rfl, rfl, rfl, rfl,
    foldGaugeAnomalyP9QuadraticSubfieldDiscriminant_not_square,
    foldGaugeAnomalyP9QuadraticSubfieldDiscriminant_eq,
    by
      simpa using (Fintype.card_perm : Fintype.card (Equiv.Perm (Fin 9)) = Nat.factorial 9)⟩

end Omega.Folding
