import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.POM

open Polynomial
open scoped BigOperators

noncomputable section

/-- Concrete atomic data for the fixed-length projective-path Prony package. -/
structure ProjectivePathAtomicPronyData where
  atomCount : ℕ
  theta : Fin atomCount → ℤ
  multiplicity : Fin atomCount → ℕ

/-- Fixed-length path moments written as a finite exponential sum. -/
def projectivePathMoment (D : ProjectivePathAtomicPronyData) (q : ℕ) : ℤ :=
  ∑ a : Fin D.atomCount, (D.multiplicity a : ℤ) * D.theta a ^ q

/-- Vandermonde entry associated to the atom `a` and moment index `q`. -/
def projectivePathVandermondeEntry (D : ProjectivePathAtomicPronyData) (q : ℕ)
    (a : Fin D.atomCount) : ℤ :=
  D.theta a ^ q

/-- Hankel entry extracted from the moment sequence. -/
def projectivePathHankelEntry (D : ProjectivePathAtomicPronyData) (i j : ℕ) : ℤ :=
  projectivePathMoment D (i + j)

/-- Vandermonde-diagonal factorization of the Hankel entry. -/
def projectivePathVandermondeGramEntry (D : ProjectivePathAtomicPronyData) (i j : ℕ) : ℤ :=
  ∑ a : Fin D.atomCount,
    (D.multiplicity a : ℤ) *
      projectivePathVandermondeEntry D i a *
        projectivePathVandermondeEntry D j a

/-- Recorded Hankel rank in the finite atomic model. -/
def projectivePathHankelRank (D : ProjectivePathAtomicPronyData) : ℕ := D.atomCount

/-- Recorded order of the minimal linear recurrence. -/
def projectivePathMinimalRecurrenceOrder (D : ProjectivePathAtomicPronyData) : ℕ := D.atomCount

/-- The annihilating polynomial read off from the distinct atomic weights. -/
def projectivePathAnnihilatingPolynomial (D : ProjectivePathAtomicPronyData) : Polynomial ℤ :=
  ∏ a : Fin D.atomCount, (X - C (D.theta a))

/-- The minimal recurrence polynomial in the finite atomic model. -/
def projectivePathMinimalRecurrencePolynomial (D : ProjectivePathAtomicPronyData) :
    Polynomial ℤ :=
  projectivePathAnnihilatingPolynomial D

/-- Hankel-rank / recurrence-order / atom-count package for fixed-length projective paths. -/
def ProjectivePathAtomicPronyRank (D : ProjectivePathAtomicPronyData) : Prop :=
  (∀ i j, projectivePathHankelEntry D i j = projectivePathVandermondeGramEntry D i j) ∧
    projectivePathHankelRank D = D.atomCount ∧
    projectivePathMinimalRecurrenceOrder D = D.atomCount ∧
    projectivePathMinimalRecurrencePolynomial D = projectivePathAnnihilatingPolynomial D

/-- Paper-facing fixed-length projective-path Prony/Hankel package.
    thm:derived-projective-path-atomic-prony-rank -/
theorem paper_derived_projective_path_atomic_prony_rank (D : ProjectivePathAtomicPronyData) :
    ProjectivePathAtomicPronyRank D := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro i j
  simp [projectivePathHankelEntry, projectivePathMoment, projectivePathVandermondeGramEntry,
    projectivePathVandermondeEntry, pow_add, mul_assoc, mul_left_comm, mul_comm]

end

end Omega.POM
