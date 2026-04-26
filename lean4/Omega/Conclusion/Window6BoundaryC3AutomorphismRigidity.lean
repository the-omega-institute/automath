import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryC3DiagonalIrreducibleSplitting

namespace Omega.Conclusion

/-- Concrete rigidity statement for `C₃`-equivariant boundary-parity automorphisms. Every such
automorphism fixes the diagonal line and is one of the three powers of the boundary rotation. -/
def conclusion_window6_boundary_c3_automorphism_rigidity_statement : Prop :=
  ∀ φ : BoundaryParityVector ≃ₗ[ZMod 2] BoundaryParityVector,
    (∀ x : BoundaryParityVector, φ (boundaryRotate x) = boundaryRotate (φ x)) →
      φ boundaryDiagonal = boundaryDiagonal ∧
        ((∀ x : BoundaryParityVector, φ x = x) ∨
          (∀ x : BoundaryParityVector, φ x = boundaryRotate x) ∨
            ∀ x : BoundaryParityVector, φ x = boundaryRotate (boundaryRotate x))

/-- Paper label: `thm:conclusion-window6-boundary-c3-automorphism-rigidity`. The previously
formalized diagonal/irreducible splitting forces every `C₃`-equivariant automorphism to fix the
diagonal line, and an explicit computation shows that the only possibilities are the three powers
of the boundary rotation. -/
theorem paper_conclusion_window6_boundary_c3_automorphism_rigidity :
    conclusion_window6_boundary_c3_automorphism_rigidity_statement := by
  intro φ hφ
  rcases paper_conclusion_window6_boundary_c3_diagonal_irreducible_splitting with
    ⟨hfixed, _⟩
  let v := φ boundaryE0
  have hdiag_rot : boundaryRotate boundaryDiagonal = boundaryDiagonal := by
    ext i
    fin_cases i <;> simp [boundaryRotate, boundaryDiagonal]
  have hφe2 : φ boundaryE2 = boundaryRotate v := by
    simpa [v, boundaryRotate_e0] using hφ boundaryE0
  have hφe1 : φ boundaryE1 = boundaryRotate (boundaryRotate v) := by
    calc
      φ boundaryE1 = boundaryRotate (φ boundaryE2) := by
        simpa [boundaryRotate_e2] using hφ boundaryE2
      _ = boundaryRotate (boundaryRotate v) := by rw [hφe2]
  have hdiag_fixed : boundaryRotate (φ boundaryDiagonal) = φ boundaryDiagonal := by
    simpa [hdiag_rot] using (hφ boundaryDiagonal).symm
  have hdiag_ne : boundaryDiagonal ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    simpa [boundaryDiagonal] using hcoord
  have hφdiag_ne : φ boundaryDiagonal ≠ 0 := by
    intro hzero
    apply hdiag_ne
    apply φ.injective
    simpa using hzero
  have hfixdiag : φ boundaryDiagonal = boundaryDiagonal := by
    rcases (hfixed (φ boundaryDiagonal)).mp hdiag_fixed with hzero | hdiag
    · exact (hφdiag_ne hzero).elim
    · exact hdiag
  have hsum : v + boundaryRotate (boundaryRotate v) + boundaryRotate v = boundaryDiagonal := by
    calc
      v + boundaryRotate (boundaryRotate v) + boundaryRotate v
          = φ boundaryE0 + φ boundaryE1 + φ boundaryE2 := by
            simp [v, hφe1, hφe2]
      _ = φ (boundaryE0 + boundaryE1 + boundaryE2) := by simp [map_add, add_assoc]
      _ = φ boundaryDiagonal := by rw [← boundaryDiagonal_eq_sum_basis]
      _ = boundaryDiagonal := hfixdiag
  have hodd : v 0 + v 1 + v 2 = 1 := by
    have hcoord := congrFun hsum 0
    change v 0 + (boundaryRotate (boundaryRotate v)) 0 + (boundaryRotate v) 0 = boundaryDiagonal 0 at hcoord
    simpa [boundaryRotate, boundaryDiagonal, add_assoc, add_left_comm, add_comm] using hcoord
  have hv0 : v 0 = 0 ∨ v 0 = 1 := by
    have hval : (v 0).val = 0 ∨ (v 0).val = 1 := by
      have hlt : (v 0).val < 2 := ZMod.val_lt (v 0)
      omega
    rcases hval with hval | hval
    · left
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
    · right
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
  have hv1 : v 1 = 0 ∨ v 1 = 1 := by
    have hval : (v 1).val = 0 ∨ (v 1).val = 1 := by
      have hlt : (v 1).val < 2 := ZMod.val_lt (v 1)
      omega
    rcases hval with hval | hval
    · left
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
    · right
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
  have hv2 : v 2 = 0 ∨ v 2 = 1 := by
    have hval : (v 2).val = 0 ∨ (v 2).val = 1 := by
      have hlt : (v 2).val < 2 := ZMod.val_lt (v 2)
      omega
    rcases hval with hval | hval
    · left
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
    · right
      simpa [ZMod.natCast_zmod_val] using congrArg (fun n : Nat => (n : ZMod 2)) hval
  have hv_class :
      v = boundaryE0 ∨ v = boundaryE1 ∨ v = boundaryE2 := by
    rcases hv0 with hv0 | hv0 <;> rcases hv1 with hv1 | hv1 <;> rcases hv2 with hv2 | hv2
    · exfalso
      have hcontra := hodd
      simp [hv0, hv1, hv2, add_assoc, add_left_comm, add_comm] at hcontra
    · right
      right
      ext i
      fin_cases i <;> simp [boundaryE2, hv0, hv1, hv2]
    · right
      left
      ext i
      fin_cases i <;> simp [boundaryE1, hv0, hv1, hv2]
    · exfalso
      have hcontra := hodd
      simp [hv0, hv1, hv2, add_assoc, add_left_comm, add_comm] at hcontra
    · left
      ext i
      fin_cases i <;> simp [boundaryE0, hv0, hv1, hv2]
    · exfalso
      have hcontra := hodd
      simp [hv0, hv1, hv2, add_assoc, add_left_comm, add_comm] at hcontra
    · exfalso
      have hcontra := hodd
      simp [hv0, hv1, hv2, add_assoc, add_left_comm, add_comm] at hcontra
    · exfalso
      have hcoord := congrFun hsum 0
      simp [boundaryRotate, boundaryDiagonal, hv0, hv1, hv2] at hcoord
      have hvdiag : v = boundaryDiagonal := by
        ext i
        fin_cases i <;> simp [boundaryDiagonal, hv0, hv1, hv2]
      have hsame : φ boundaryE0 = φ boundaryE2 := by
        calc
          φ boundaryE0 = boundaryDiagonal := hvdiag
          _ = boundaryRotate boundaryDiagonal := by
            ext i
            fin_cases i <;> simp [boundaryRotate, boundaryDiagonal]
          _ = boundaryRotate v := by simpa [hvdiag]
          _ = φ boundaryE2 := hφe2.symm
      have hneq : boundaryE0 ≠ boundaryE2 := by
        intro hEq
        have hcoord := congrFun hEq 0
        simp [boundaryE0, boundaryE2] at hcoord
      exact hneq (φ.injective hsame)
  refine ⟨hfixdiag, ?_⟩
  rcases hv_class with hve0 | hve1 | hve2
  · left
    intro x
    have hE0 : φ boundaryE0 = boundaryE0 := hve0
    have hE2 : φ boundaryE2 = boundaryE2 := by simpa [hve0] using hφe2
    have hE1 : φ boundaryE1 = boundaryE1 := by simpa [hve0] using hφe1
    calc
      φ x = φ (x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2) := by
        conv_lhs => rw [boundaryVector_eq_sum_basis x]
      _ = x 0 • φ boundaryE0 + x 1 • φ boundaryE1 + x 2 • φ boundaryE2 := by simp
      _ = x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2 := by rw [hE0, hE1, hE2]
      _ = x := by symm; exact boundaryVector_eq_sum_basis x
  · right
    right
    intro x
    have hE0 : φ boundaryE0 = boundaryE1 := hve1
    have hE2 : φ boundaryE2 = boundaryE0 := by simpa [hve1] using hφe2
    have hE1 : φ boundaryE1 = boundaryE2 := by simpa [hve1] using hφe1
    calc
      φ x = φ (x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2) := by
        conv_lhs => rw [boundaryVector_eq_sum_basis x]
      _ = x 0 • φ boundaryE0 + x 1 • φ boundaryE1 + x 2 • φ boundaryE2 := by simp
      _ = x 0 • boundaryE1 + x 1 • boundaryE2 + x 2 • boundaryE0 := by rw [hE0, hE1, hE2]
      _ = boundaryRotate (boundaryRotate x) := by
        ext i
        fin_cases i <;> simp [boundaryRotate, boundaryE0, boundaryE1, boundaryE2]
  · right
    left
    intro x
    have hE0 : φ boundaryE0 = boundaryE2 := hve2
    have hE2 : φ boundaryE2 = boundaryE1 := by simpa [hve2] using hφe2
    have hE1 : φ boundaryE1 = boundaryE0 := by simpa [hve2] using hφe1
    calc
      φ x = φ (x 0 • boundaryE0 + x 1 • boundaryE1 + x 2 • boundaryE2) := by
        conv_lhs => rw [boundaryVector_eq_sum_basis x]
      _ = x 0 • φ boundaryE0 + x 1 • φ boundaryE1 + x 2 • φ boundaryE2 := by simp
      _ = x 0 • boundaryE2 + x 1 • boundaryE0 + x 2 • boundaryE1 := by rw [hE0, hE1, hE2]
      _ = boundaryRotate x := by
        ext i
        fin_cases i <;> simp [boundaryRotate, boundaryE0, boundaryE1, boundaryE2]

end Omega.Conclusion
