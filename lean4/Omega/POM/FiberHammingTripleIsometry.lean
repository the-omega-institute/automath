import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff

namespace Omega.POM

open scoped symmDiff

/-- Concrete proxy for the independent-set side of the fiber correspondence. -/
abbrev pom_fiber_hamming_triple_isometry_independent_set := Finset ℕ

/-- The canonical correspondence sends a fiber configuration to its chosen independent set. In
this concrete model the datum is already recorded by that finite set. -/
def pom_fiber_hamming_triple_isometry_fiber_to_independent_set
    (S : pom_fiber_hamming_triple_isometry_independent_set) :
    pom_fiber_hamming_triple_isometry_independent_set :=
  S

/-- Each selected site contributes one disjoint local block of length `3`. -/
def pom_fiber_hamming_triple_isometry_fiber_word
    (S : pom_fiber_hamming_triple_isometry_independent_set) : Finset (ℕ × Fin 3) :=
  (pom_fiber_hamming_triple_isometry_fiber_to_independent_set S).product Finset.univ

/-- Hamming distance on the concrete fiber model is the size of the symmetric difference of the
corresponding length-`3` local blocks. -/
def pom_fiber_hamming_triple_isometry_hamming_distance
    (S T : pom_fiber_hamming_triple_isometry_independent_set) : Nat :=
  ((pom_fiber_hamming_triple_isometry_fiber_word S) ∆
    (pom_fiber_hamming_triple_isometry_fiber_word T)).card

/-- Paper-facing statement: the concrete fiber correspondence is a triple isometry because every
site in the symmetric difference toggles exactly one disjoint block of length `3`. -/
def paper_pom_fiber_hamming_triple_isometry_stmt : Prop :=
  ∀ S T : pom_fiber_hamming_triple_isometry_independent_set,
    pom_fiber_hamming_triple_isometry_hamming_distance S T =
      3 *
        ((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
          (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).card

private lemma pom_fiber_hamming_triple_isometry_fiber_word_symmDiff
    (S T : pom_fiber_hamming_triple_isometry_independent_set) :
    ((pom_fiber_hamming_triple_isometry_fiber_word S) ∆
        (pom_fiber_hamming_triple_isometry_fiber_word T)) =
      ((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
          (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).product Finset.univ := by
  ext x
  rcases x with ⟨i, j⟩
  by_cases hS : i ∈ pom_fiber_hamming_triple_isometry_fiber_to_independent_set S <;>
    by_cases hT : i ∈ pom_fiber_hamming_triple_isometry_fiber_to_independent_set T <;>
    simp [Finset.mem_symmDiff, pom_fiber_hamming_triple_isometry_fiber_word,
      pom_fiber_hamming_triple_isometry_fiber_to_independent_set]

theorem paper_pom_fiber_hamming_triple_isometry : paper_pom_fiber_hamming_triple_isometry_stmt := by
  intro S T
  have hcard3 : (Finset.univ : Finset (Fin 3)).card = 3 := by
    decide
  calc
    pom_fiber_hamming_triple_isometry_hamming_distance S T
      = (((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
            (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).product
          (Finset.univ : Finset (Fin 3))).card := by
            rw [pom_fiber_hamming_triple_isometry_hamming_distance,
              pom_fiber_hamming_triple_isometry_fiber_word_symmDiff]
    _ =
        ((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
            (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).card *
          (Finset.univ : Finset (Fin 3)).card := by
            simp
    _ =
        ((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
            (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).card *
          3 := by
            rw [hcard3]
    _ =
        3 *
          ((pom_fiber_hamming_triple_isometry_fiber_to_independent_set S) ∆
            (pom_fiber_hamming_triple_isometry_fiber_to_independent_set T)).card := by
            simp [Nat.mul_comm]

end Omega.POM
