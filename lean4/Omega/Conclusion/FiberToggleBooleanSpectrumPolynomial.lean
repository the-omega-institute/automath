import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

open Polynomial
open scoped BigOperators

/-- The symbolic sector idempotent indexed by a subset `S ⊆ [r]`. -/
def toggleSectorIdempotent (r : Nat) (S : Finset (Fin r)) : Finset (Fin r) → ℤ :=
  fun T => if T = S then 1 else 0

/-- Orthogonality of the symbolic sector idempotents. -/
def toggleSectorIdempotentOrthogonal (r : Nat) : Prop :=
  ∀ S T : Finset (Fin r),
    toggleSectorIdempotent r S * toggleSectorIdempotent r T =
      if S = T then toggleSectorIdempotent r S else 0

/-- Completeness of the symbolic sector idempotents. -/
def toggleSectorIdempotentComplete (r : Nat) : Prop :=
  ∑ S : Finset (Fin r), toggleSectorIdempotent r S = 1

/-- Recursive dimension-generating polynomial obtained by adding one toggle component at a time. -/
def toggleDimensionGeneratingPolynomial : List Nat → Polynomial ℤ
  | [] => 1
  | n :: ns =>
      toggleDimensionGeneratingPolynomial ns +
        Polynomial.C ((n : ℤ) - 1) * X * toggleDimensionGeneratingPolynomial ns

/-- Closed-form Boolean spectrum polynomial. -/
def toggleBooleanSpectrumPolynomial : List Nat → Polynomial ℤ
  | [] => 1
  | n :: ns =>
      (1 + Polynomial.C ((n : ℤ) - 1) * X) * toggleBooleanSpectrumPolynomial ns

/-- Paper-facing package for the Boolean sector spectrum polynomial. -/
def ConclusionFiberToggleBooleanSpectrumPolynomial (lengths : List Nat) : Prop :=
  toggleSectorIdempotentOrthogonal lengths.length ∧
    toggleSectorIdempotentComplete lengths.length ∧
    toggleDimensionGeneratingPolynomial lengths = toggleBooleanSpectrumPolynomial lengths ∧
    (toggleBooleanSpectrumPolynomial lengths).eval 1 = (lengths.map fun n => (n : ℤ)).prod

private theorem toggleSectorIdempotent_orthogonal (r : Nat) :
    toggleSectorIdempotentOrthogonal r := by
  intro S T
  ext U
  by_cases hST : S = T
  · subst hST
    by_cases hUS : U = S
    · simp [toggleSectorIdempotent, hUS]
    · simp [toggleSectorIdempotent, hUS]
  · by_cases hUS : U = S
    · have hUT : U ≠ T := by
        intro hUT
        apply hST
        simpa [hUS] using hUT
      simp [toggleSectorIdempotent, hST, hUS]
    · simp [toggleSectorIdempotent, hST, hUS]

private theorem toggleSectorIdempotent_complete (r : Nat) :
    toggleSectorIdempotentComplete r := by
  ext U
  simp [toggleSectorIdempotent]

private theorem toggleDimensionGeneratingPolynomial_eq_closed_form (lengths : List Nat) :
    toggleDimensionGeneratingPolynomial lengths = toggleBooleanSpectrumPolynomial lengths := by
  induction lengths with
  | nil =>
      simp [toggleDimensionGeneratingPolynomial, toggleBooleanSpectrumPolynomial]
  | cons n ns ih =>
      rw [toggleDimensionGeneratingPolynomial, toggleBooleanSpectrumPolynomial, ih]
      ring

private theorem toggleBooleanSpectrumPolynomial_eval_one (lengths : List Nat) :
    (toggleBooleanSpectrumPolynomial lengths).eval 1 = (lengths.map fun n => (n : ℤ)).prod := by
  induction lengths with
  | nil =>
      simp [toggleBooleanSpectrumPolynomial]
  | cons n ns ih =>
      simp [toggleBooleanSpectrumPolynomial, ih]

/-- Paper label: `thm:conclusion-fiber-toggle-boolean-spectrum-polynomial`. -/
theorem paper_conclusion_fiber_toggle_boolean_spectrum_polynomial (lengths : List Nat) :
    ConclusionFiberToggleBooleanSpectrumPolynomial lengths := by
  refine ⟨toggleSectorIdempotent_orthogonal lengths.length,
    toggleSectorIdempotent_complete lengths.length, ?_, ?_⟩
  · exact toggleDimensionGeneratingPolynomial_eq_closed_form lengths
  · exact toggleBooleanSpectrumPolynomial_eval_one lengths

end

end Omega.Conclusion
