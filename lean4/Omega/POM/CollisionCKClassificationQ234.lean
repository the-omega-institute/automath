import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Folding.CollisionKernel
import Omega.POM.CollisionCKFibonacci

namespace Omega.POM

/-- Explicit integer witness showing that the `A₃` unit class dies in the Bowen--Franks cokernel
model. -/
def pom_collision_ck_classification_q234_a3_unit_witness : Fin 3 → ℤ :=
  ![3, 0, -1]

/-- The corresponding all-ones unit vector. -/
def pom_collision_ck_classification_q234_a3_unit_target : Fin 3 → ℤ :=
  ![1, 1, 1]

/-- The audited adjugate-vector coordinates from the `A₄(t)` unit-class computation. -/
def pom_collision_ck_classification_q234_a4_adjugate_vector_gcd (t : ℕ) : ℤ :=
  Int.gcd (-(3 * (t : ℤ) + 4))
    (Int.gcd (-1)
      (Int.gcd (4 * ((t : ℤ) + 1))
        (Int.gcd (-(2 * (t : ℤ) + 3)) (-((t : ℤ) + 2)))))

/-- Lean-side collision-CK classification package for the low-rank kernels `q = 2,3,4`.
The concrete content records the Cuntz parameters, the Bowen--Franks determinant sizes for
`A₂,A₃,A₄`, the explicit `A₃` unit-class witness, the `A₄(t)` determinant formula at `x = 1`,
and the adjugate-vector gcd certificate forcing the `A₄(t)` unit class to be primitive. -/
def pomCollisionCKClassificationQ234Claim (t : ℕ) : Prop :=
  Omega.POM.CollisionCKFibonacci.cuntzParam 2 = 2 ∧
    Omega.POM.CollisionCKFibonacci.cuntzParam 3 = 4 ∧
    Omega.POM.CollisionCKFibonacci.cuntzParam 4 = 9 ∧
    Int.natAbs Omega.bowenFranksMatrix2.det = 1 ∧
    Int.natAbs Omega.bowenFranksMatrix3.det = 3 ∧
    Int.natAbs Omega.bowenFranksMatrix4.det = 8 ∧
    Omega.bowenFranksMatrix3.transpose.mulVec
        pom_collision_ck_classification_q234_a3_unit_witness =
      pom_collision_ck_classification_q234_a3_unit_target ∧
    Omega.a4CharPoly (t : ℤ) 1 = -((t : ℤ) + 1) ∧
    Int.natAbs (Omega.a4CharPoly (t : ℤ) 1) = t + 1 ∧
    pom_collision_ck_classification_q234_a4_adjugate_vector_gcd t = 1

/-- Paper label: `prop:pom-collision-ck-classification-q234`. -/
theorem paper_pom_collision_ck_classification_q234 (t : ℕ) :
    pomCollisionCKClassificationQ234Claim t := by
  rcases Omega.POM.CollisionCKFibonacci.cuntzParam_seeds with ⟨h2, h3, h4, _, _⟩
  refine ⟨h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Omega.bowenFranksMatrix2_det]
  · simpa [Omega.bowenFranksMatrix3_det]
  · simpa [Omega.bowenFranksMatrix4_det]
  · native_decide
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Omega.a4CharPoly_at_one (t := (t : ℤ)))
  · rw [Omega.a4CharPoly_at_one]
    have hcast : (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) := by norm_num
    rw [show (-1 : ℤ) - (t : ℤ) = -((t : ℤ) + 1) by ring, Int.natAbs_neg]
    rw [hcast, Int.natAbs_natCast]
  · unfold pom_collision_ck_classification_q234_a4_adjugate_vector_gcd
    rw [show
      Int.gcd (-1)
          (Int.gcd (4 * ((t : ℤ) + 1)) (Int.gcd (-(2 * (t : ℤ) + 3)) (-((t : ℤ) + 2)))) = 1 by
      simp]
    simp

end Omega.POM
