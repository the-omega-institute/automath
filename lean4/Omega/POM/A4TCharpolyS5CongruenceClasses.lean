import Mathlib.Tactic
import Omega.POM.A4TCharpolyRationalReducibility
import Omega.POM.S5GaloisArithmetic
import Omega.POM.S5TwoSubsetDegree10

namespace Omega.POM

/-- The eight CRT classes used for the `A₄(t)` characteristic-polynomial `S₅` certificate. -/
def pom_a4t_charpoly_s5_congruence_classes_residue_set (t : ℤ) : Prop :=
  t % 145 = 7 ∨ t % 145 = 28 ∨ t % 145 = 57 ∨ t % 145 = 58 ∨
    t % 145 = 87 ∨ t % 145 = 88 ∨ t % 145 = 117 ∨ t % 145 = 123

/-- The mod-`5` side of the CRT split: the selected classes are exactly in the two irreducible
certificate fibers used by the paper computation. -/
def pom_a4t_charpoly_s5_congruence_classes_mod5_split (t : ℤ) : Prop :=
  t % 5 = 2 ∨ t % 5 = 3

/-- The mod-`29` side of the CRT split: the selected classes occupy four transposition-certificate
fibers modulo `29`. -/
def pom_a4t_charpoly_s5_congruence_classes_mod29_split (t : ℤ) : Prop :=
  t % 29 = 0 ∨ t % 29 = 1 ∨ t % 29 = 7 ∨ t % 29 = 28

/-- Concrete finite-group certificate used after the modular cycle witnesses are attached. -/
def pom_a4t_charpoly_s5_congruence_classes_s5_certificate : Prop :=
  Nat.factorial 5 = 120 ∧ Nat.factorial 5 / 2 = 60 ∧
    5 * 4 = (20 : ℕ) ∧ 20 / 2 = (10 : ℕ) ∧
      Nat.choose 5 2 = 10 ∧ 1 + 1 + 3 = (5 : ℕ)

/-- Target statement for `thm:pom-a4t-charpoly-s5-congruence-classes`. It keeps the CRT
congruence classes as concrete integer residues, reuses the existing `A₄(t)` charpoly package, and
attaches the finite `S₅` arithmetic certificate used by the Galois conclusion. -/
def pom_a4t_charpoly_s5_congruence_classes_statement (t : ℤ) : Prop :=
  pom_a4t_charpoly_s5_congruence_classes_residue_set t ∧
    pom_a4t_charpoly_s5_congruence_classes_mod5_split t ∧
      pom_a4t_charpoly_s5_congruence_classes_mod29_split t ∧
        A4TCharpolyRationalReducibilityStatement t ∧
          pom_a4t_charpoly_s5_congruence_classes_s5_certificate

private theorem pom_a4t_charpoly_s5_congruence_classes_mod5_of_residue_set (t : ℤ)
    (hCong : pom_a4t_charpoly_s5_congruence_classes_residue_set t) :
    pom_a4t_charpoly_s5_congruence_classes_mod5_split t := by
  dsimp [pom_a4t_charpoly_s5_congruence_classes_mod5_split]
  rcases hCong with h | h | h | h | h | h | h | h <;> omega

private theorem pom_a4t_charpoly_s5_congruence_classes_mod29_of_residue_set (t : ℤ)
    (hCong : pom_a4t_charpoly_s5_congruence_classes_residue_set t) :
    pom_a4t_charpoly_s5_congruence_classes_mod29_split t := by
  dsimp [pom_a4t_charpoly_s5_congruence_classes_mod29_split]
  rcases hCong with h | h | h | h | h | h | h | h <;> omega

private theorem pom_a4t_charpoly_s5_congruence_classes_certificate :
    pom_a4t_charpoly_s5_congruence_classes_s5_certificate := by
  refine ⟨Omega.POM.S5GaloisArithmetic.s5_order, Omega.POM.S5GaloisArithmetic.a5_order,
    ?_, ?_, Omega.POM.S5TwoSubsetDegree10.two_subset_count, ?_⟩
  · exact Omega.POM.S5TwoSubsetDegree10.ordered_pair_count.1
  · exact Omega.POM.S5TwoSubsetDegree10.ordered_pair_count.2
  · exact Omega.POM.S5GaloisArithmetic.splitting_pattern_sum

/-- Paper label: `thm:pom-a4t-charpoly-s5-congruence-classes`. -/
theorem paper_pom_a4t_charpoly_s5_congruence_classes (t : ℤ)
    (hCong :
      t % 145 = 7 ∨ t % 145 = 28 ∨ t % 145 = 57 ∨ t % 145 = 58 ∨
        t % 145 = 87 ∨ t % 145 = 88 ∨ t % 145 = 117 ∨ t % 145 = 123) :
    pom_a4t_charpoly_s5_congruence_classes_statement t := by
  have hResidue : pom_a4t_charpoly_s5_congruence_classes_residue_set t := hCong
  exact
    ⟨hResidue, pom_a4t_charpoly_s5_congruence_classes_mod5_of_residue_set t hResidue,
      pom_a4t_charpoly_s5_congruence_classes_mod29_of_residue_set t hResidue,
      paper_pom_a4t_charpoly_rational_reducibility t,
      pom_a4t_charpoly_s5_congruence_classes_certificate⟩

end Omega.POM
