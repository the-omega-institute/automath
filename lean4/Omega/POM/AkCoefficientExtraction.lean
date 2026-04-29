import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic

namespace Omega.POM

open scoped BigOperators
open Classical

noncomputable section

/-- A bounded per-state choice table: for each state `q`, choose how many of the `ν q`
copies take the `false` branch. -/
abbrev pom_ak_coefficient_extraction_choiceFamily {Q : Type} (nu : Q → ℕ) :=
  (q : Q) → Fin (nu q + 1)

/-- Read a bounded choice as a natural-number count. -/
def pom_ak_coefficient_extraction_choiceCount {Q : Type} {nu : Q → ℕ}
    (a : pom_ak_coefficient_extraction_choiceFamily nu) (q : Q) : ℕ :=
  a q

/-- A choice table is compatible with a requested output bit when every disallowed branch is
forced to have zero multiplicity. -/
def pom_ak_coefficient_extraction_admissible {Q : Type} (eps : Q → Bool → Bool)
    (e : Bool) (nu : Q → ℕ) (a : pom_ak_coefficient_extraction_choiceFamily nu) : Prop :=
  ∀ q,
    (eps q false ≠ e → pom_ak_coefficient_extraction_choiceCount a q = 0) ∧
      (eps q true ≠ e → pom_ak_coefficient_extraction_choiceCount a q = nu q) ∧
      pom_ak_coefficient_extraction_choiceCount a q ≤ nu q

/-- Aggregate a per-state branch choice into the resulting histogram. -/
def pom_ak_coefficient_extraction_nextHistogram {Q : Type} [Fintype Q] [DecidableEq Q]
    (delta : Q → Bool → Q) (nu : Q → ℕ)
    (a : pom_ak_coefficient_extraction_choiceFamily nu) : Q → ℕ :=
  fun q' =>
    Finset.sum Finset.univ fun q : Q =>
      (if delta q false = q' then pom_ak_coefficient_extraction_choiceCount a q else 0) +
        (if delta q true = q' then
          nu q - pom_ak_coefficient_extraction_choiceCount a q
        else
          0)

/-- The binomial multiplicity contributed by a compatible branch-count table. -/
def pom_ak_coefficient_extraction_choiceWeight {Q : Type} [Fintype Q]
    (nu : Q → ℕ) (a : pom_ak_coefficient_extraction_choiceFamily nu) : ℕ :=
  Finset.prod Finset.univ fun q : Q =>
    Nat.choose (nu q) (pom_ak_coefficient_extraction_choiceCount a q)

/-- The one-step transition weight is the finite binomial convolution over all branch-count
tables that aggregate to the requested target histogram. -/
def pom_ak_coefficient_extraction_transitionWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (delta : Q → Bool → Q) (eps : Q → Bool → Bool) (e : Bool)
    (nu nu' : Q → ℕ) : ℕ :=
  Finset.sum (Finset.univ : Finset (pom_ak_coefficient_extraction_choiceFamily nu)) fun a =>
    if pom_ak_coefficient_extraction_admissible eps e nu a ∧
        pom_ak_coefficient_extraction_nextHistogram delta nu a = nu'
    then
      pom_ak_coefficient_extraction_choiceWeight nu a
    else
      0

/-- A coefficient table for the multivariate generating function, indexed by target histograms. -/
abbrev pom_ak_coefficient_extraction_coefficientTable (Q : Type) := (Q → ℕ) → ℕ

/-- The generating function is represented by its coefficient table.  Its entries are exactly the
finite product convolution coefficients. -/
def pom_ak_coefficient_extraction_generatingFunction {Q : Type} [Fintype Q] [DecidableEq Q]
    (delta : Q → Bool → Q) (eps : Q → Bool → Bool) (e : Bool)
    (nu : Q → ℕ) : pom_ak_coefficient_extraction_coefficientTable Q :=
  fun nu' => pom_ak_coefficient_extraction_transitionWeight delta eps e nu nu'

/-- Coefficient extraction from the table representation of the generating function. -/
def pom_ak_coefficient_extraction_coeff {Q : Type}
    (F : pom_ak_coefficient_extraction_coefficientTable Q) (nu' : Q → ℕ) : ℕ :=
  F nu'

theorem paper_pom_ak_coefficient_extraction {Q : Type} [Fintype Q] [DecidableEq Q]
    (delta : Q → Bool → Q) (eps : Q → Bool → Bool) (e : Bool) (nu nu' : Q → ℕ) :
    pom_ak_coefficient_extraction_transitionWeight delta eps e nu nu' =
      pom_ak_coefficient_extraction_coeff
        (pom_ak_coefficient_extraction_generatingFunction delta eps e nu) nu' := by
  rfl

end

end Omega.POM
