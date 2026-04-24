import Mathlib.Tactic

namespace Omega.Conclusion

abbrev BoundaryParityVector := Fin 3 → ZMod 2

def boundaryRotate (x : BoundaryParityVector) : BoundaryParityVector :=
  ![x 1, x 2, x 0]

def boundaryDiagonal : BoundaryParityVector := ![1, 1, 1]

def boundaryE0 : BoundaryParityVector := ![1, 0, 0]
def boundaryE1 : BoundaryParityVector := ![0, 1, 0]
def boundaryE2 : BoundaryParityVector := ![0, 0, 1]

def BoundaryParityC3DiagonalIrreducibleSplittingLaw : Prop :=
  (∀ x : BoundaryParityVector, boundaryRotate x = x ↔ x = 0 ∨ x = boundaryDiagonal) ∧
  ∀ φ : BoundaryParityVector →ₗ[ZMod 2] ZMod 2,
    (∀ x : BoundaryParityVector, φ (boundaryRotate x) = φ x) →
      φ boundaryDiagonal = 0 → φ = 0

lemma boundaryRotate_e0 : boundaryRotate boundaryE0 = boundaryE2 := by
  ext i
  fin_cases i <;> simp [boundaryRotate, boundaryE0, boundaryE2]

lemma boundaryRotate_e1 : boundaryRotate boundaryE1 = boundaryE0 := by
  ext i
  fin_cases i <;> simp [boundaryRotate, boundaryE0, boundaryE1]

lemma boundaryRotate_e2 : boundaryRotate boundaryE2 = boundaryE1 := by
  ext i
  fin_cases i <;> simp [boundaryRotate, boundaryE1, boundaryE2]

lemma boundaryDiagonal_eq_sum_basis :
    boundaryDiagonal = boundaryE0 + boundaryE1 + boundaryE2 := by
  ext i
  fin_cases i <;> simp [boundaryDiagonal, boundaryE0, boundaryE1, boundaryE2]

lemma boundaryVector_eq_sum_basis (x : BoundaryParityVector) :
    x = x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2 := by
  ext i
  fin_cases i <;> simp [boundaryE0, boundaryE1, boundaryE2]

lemma boundaryRotate_fixed_iff (x : BoundaryParityVector) :
    boundaryRotate x = x ↔ x = 0 ∨ x = boundaryDiagonal := by
  constructor
  · intro hx
    have h10 : x 1 = x 0 := by
      simpa [boundaryRotate] using congrFun hx 0
    have h21 : x 2 = x 1 := by
      simpa [boundaryRotate] using congrFun hx 1
    have hx0_cases : x 0 = 0 ∨ x 0 = 1 := by
      have hval : (x 0).val = 0 ∨ (x 0).val = 1 := by
        have hlt : (x 0).val < 2 := ZMod.val_lt (x 0)
        omega
      rcases hval with hval | hval
      · left
        simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
      · right
        simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
    rcases hx0_cases with hx0 | hx0
    · left
      ext i
      fin_cases i <;> simp [h10, h21, hx0]
    · right
      ext i
      fin_cases i <;> simp [boundaryDiagonal, h10, h21, hx0]
  · rintro (rfl | rfl)
    · ext i
      fin_cases i <;> simp [boundaryRotate]
    · ext i
      fin_cases i <;> simp [boundaryRotate, boundaryDiagonal]

theorem paper_conclusion_window6_boundary_c3_diagonal_irreducible_splitting :
    BoundaryParityC3DiagonalIrreducibleSplittingLaw := by
  refine ⟨boundaryRotate_fixed_iff, ?_⟩
  intro φ hφ hdiag
  have h01 : φ boundaryE0 = φ boundaryE1 := by
    simpa [boundaryRotate_e1] using hφ boundaryE1
  have h12 : φ boundaryE1 = φ boundaryE2 := by
    simpa [boundaryRotate_e2] using hφ boundaryE2
  have hdiag_eval : φ boundaryDiagonal = φ boundaryE0 := by
    have hdouble : φ boundaryE0 + φ boundaryE0 = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    calc
      φ boundaryDiagonal = φ (boundaryE0 + boundaryE1 + boundaryE2) := by
        rw [boundaryDiagonal_eq_sum_basis]
      _ = φ boundaryE0 + φ boundaryE1 + φ boundaryE2 := by simp
      _ = φ boundaryE0 + φ boundaryE0 + φ boundaryE0 := by rw [h01, h12]
      _ = (φ boundaryE0 + φ boundaryE0) + φ boundaryE0 := by abel
      _ = φ boundaryE0 := by rw [hdouble, zero_add]
  have hE0 : φ boundaryE0 = 0 := by
    rw [← hdiag_eval, hdiag]
  have hE1 : φ boundaryE1 = 0 := by rw [← h01, hE0]
  have hE2 : φ boundaryE2 = 0 := by rw [← h12, hE1]
  apply LinearMap.ext
  intro x
  calc
    φ x = φ (x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2) := by
      conv_lhs => rw [boundaryVector_eq_sum_basis x]
    _ = x 0 * φ boundaryE0 + x 1 * φ boundaryE1 + x 2 * φ boundaryE2 := by simp
    _ = x 0 * φ boundaryE0 + (x 1 * φ boundaryE1 + x 2 * φ boundaryE2) := by rw [add_assoc]
    _ = 0 := by simp [hE0, hE1, hE2]

end Omega.Conclusion
