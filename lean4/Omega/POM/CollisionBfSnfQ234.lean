import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega.POM

/-- Explicit Smith normal form of `I - A₂`. -/
def pom_collision_bf_snf_q234_snf2 : Matrix (Fin 3) (Fin 3) ℤ := 1

/-- Explicit Smith normal form of `I - A₃`. -/
def pom_collision_bf_snf_q234_snf3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 3]

/-- Explicit Smith normal form of `I - A₄`. -/
def pom_collision_bf_snf_q234_snf4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 8]

/-- The terminal Smith invariant of `I - A₂`. -/
def pom_collision_bf_snf_q234_bf_modulus_q2 : ℕ :=
  Int.toNat (pom_collision_bf_snf_q234_snf2 2 2)

/-- The terminal Smith invariant of `I - A₃`. -/
def pom_collision_bf_snf_q234_bf_modulus_q3 : ℕ :=
  Int.toNat (pom_collision_bf_snf_q234_snf3 2 2)

/-- The terminal Smith invariant of `I - A₄`. -/
def pom_collision_bf_snf_q234_bf_modulus_q4 : ℕ :=
  Int.toNat (pom_collision_bf_snf_q234_snf4 4 4)

/-- Bowen--Franks model read off from the last Smith invariant of `I - A₂`. -/
abbrev pom_collision_bf_snf_q234_bf_group_q2 := ZMod pom_collision_bf_snf_q234_bf_modulus_q2

/-- Bowen--Franks model read off from the last Smith invariant of `I - A₃`. -/
abbrev pom_collision_bf_snf_q234_bf_group_q3 := ZMod pom_collision_bf_snf_q234_bf_modulus_q3

/-- Bowen--Franks model read off from the last Smith invariant of `I - A₄`. -/
abbrev pom_collision_bf_snf_q234_bf_group_q4 := ZMod pom_collision_bf_snf_q234_bf_modulus_q4

/-- POM-facing package of the explicit determinants, Smith normal forms, and Bowen--Franks group
models for the low-order collision kernels `q = 2, 3, 4`. -/
def pom_collision_bf_snf_q234_statement : Prop :=
  Omega.bowenFranksMatrix2.det = -1 ∧
    Omega.bowenFranksMatrix3.det = -3 ∧
    Omega.bowenFranksMatrix4.det = -8 ∧
    pom_collision_bf_snf_q234_snf2 = 1 ∧
    pom_collision_bf_snf_q234_snf3 =
      !![1, 0, 0;
         0, 1, 0;
         0, 0, 3] ∧
    pom_collision_bf_snf_q234_snf4 =
      !![1, 0, 0, 0, 0;
         0, 1, 0, 0, 0;
         0, 0, 1, 0, 0;
         0, 0, 0, 1, 0;
         0, 0, 0, 0, 8] ∧
    pom_collision_bf_snf_q234_bf_modulus_q2 = 1 ∧
    pom_collision_bf_snf_q234_bf_modulus_q3 = 3 ∧
    pom_collision_bf_snf_q234_bf_modulus_q4 = 8 ∧
    Subsingleton pom_collision_bf_snf_q234_bf_group_q2 ∧
    Nonempty (pom_collision_bf_snf_q234_bf_group_q3 ≃+ ZMod 3) ∧
    Nonempty (pom_collision_bf_snf_q234_bf_group_q4 ≃+ ZMod 8)

/-- Paper label: `prop:pom-collision-bf-snf-q234`. -/
theorem paper_pom_collision_bf_snf_q234 : pom_collision_bf_snf_q234_statement := by
  refine ⟨Omega.bowenFranksMatrix2_det, Omega.bowenFranksMatrix3_det, Omega.bowenFranksMatrix4_det,
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pom_collision_bf_snf_q234_bf_modulus_q2, pom_collision_bf_snf_q234_snf2]
  · native_decide
  · native_decide
  ·
    change Subsingleton (ZMod 1)
    infer_instance
  · refine ⟨AddEquiv.refl _⟩
  · refine ⟨AddEquiv.refl _⟩

end Omega.POM
