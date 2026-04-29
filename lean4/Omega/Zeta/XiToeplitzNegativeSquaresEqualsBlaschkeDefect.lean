import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-defect certificate connecting Toeplitz negative squares with the finite
Blaschke defect. The Boolean flag records the RH-zero-defect predicate without introducing a
new analytic API. -/
structure xi_toeplitz_negative_squares_equals_blaschke_defect_data where
  blaschkeDegree : ℕ
  negativeSquares : ℕ → ℕ
  eventualEqualityIndex : ℕ
  rhZeroDefectFlag : Bool
  negativeSquareBound : ∀ n, negativeSquares n ≤ blaschkeDegree
  eventualEquality :
    ∀ n, eventualEqualityIndex ≤ n → negativeSquares n = blaschkeDegree
  rhZeroDefectEquiv : rhZeroDefectFlag = true ↔ blaschkeDegree = 0

/-- Stable equality of Toeplitz negative squares with the finite Blaschke defect. -/
def xi_toeplitz_negative_squares_equals_blaschke_defect_stable_inertia
    (D : xi_toeplitz_negative_squares_equals_blaschke_defect_data) : Prop :=
  ∀ n, D.eventualEqualityIndex ≤ n → D.negativeSquares n = D.blaschkeDegree

/-- Concrete statement of the finite-defect Toeplitz certificate. -/
def xi_toeplitz_negative_squares_equals_blaschke_defect_statement
    (D : xi_toeplitz_negative_squares_equals_blaschke_defect_data) : Prop :=
  (∀ n, D.negativeSquares n ≤ D.blaschkeDegree) ∧
    xi_toeplitz_negative_squares_equals_blaschke_defect_stable_inertia D ∧
      (D.rhZeroDefectFlag = true ↔ D.blaschkeDegree = 0) ∧
        (D.rhZeroDefectFlag = true ↔
          ∀ n, D.eventualEqualityIndex ≤ n → D.negativeSquares n = 0)

/-- Paper label: `thm:xi-toeplitz-negative-squares-equals-blaschke-defect`. -/
theorem paper_xi_toeplitz_negative_squares_equals_blaschke_defect
    (D : xi_toeplitz_negative_squares_equals_blaschke_defect_data) :
    xi_toeplitz_negative_squares_equals_blaschke_defect_statement D := by
  refine ⟨D.negativeSquareBound, D.eventualEquality, D.rhZeroDefectEquiv, ?_⟩
  constructor
  · intro hRH n hn
    have hdegree : D.blaschkeDegree = 0 := D.rhZeroDefectEquiv.mp hRH
    rw [D.eventualEquality n hn, hdegree]
  · intro hzero
    exact D.rhZeroDefectEquiv.mpr ((D.eventualEquality D.eventualEqualityIndex le_rfl).symm.trans
      (hzero D.eventualEqualityIndex le_rfl))

end Omega.Zeta
