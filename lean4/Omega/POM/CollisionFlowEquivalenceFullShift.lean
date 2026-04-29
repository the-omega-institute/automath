import Mathlib.Tactic
import Omega.POM.CollisionCKClassificationQ234

namespace Omega.POM

/-- The Bowen--Franks determinant of the one-vertex full `N`-shift. -/
def pom_collision_flow_equivalence_full_shift_full_shift_det (N : ℕ) : ℤ :=
  1 - N

/-- The Bowen--Franks group size of the one-vertex full `N`-shift. -/
def pom_collision_flow_equivalence_full_shift_full_shift_bf_size (N : ℕ) : ℕ :=
  N - 1

/-- Concrete low-rank package matching the `q = 2,3,4` audited kernels with the full `2`-, `4`-,
and `9`-shift Franks invariants. -/
def pom_collision_flow_equivalence_full_shift_claim : Prop :=
  pomCollisionCKClassificationQ234Claim 7 ∧
    Omega.POM.CollisionCKFibonacci.cuntzParam 2 = 2 ∧
    Omega.POM.CollisionCKFibonacci.cuntzParam 3 = 4 ∧
    Omega.POM.CollisionCKFibonacci.cuntzParam 4 = 9 ∧
    Omega.bowenFranksMatrix2.det = pom_collision_flow_equivalence_full_shift_full_shift_det 2 ∧
    Omega.bowenFranksMatrix3.det = pom_collision_flow_equivalence_full_shift_full_shift_det 4 ∧
    Omega.bowenFranksMatrix4.det = pom_collision_flow_equivalence_full_shift_full_shift_det 9 ∧
    Int.natAbs Omega.bowenFranksMatrix2.det =
      pom_collision_flow_equivalence_full_shift_full_shift_bf_size 2 ∧
    Int.natAbs Omega.bowenFranksMatrix3.det =
      pom_collision_flow_equivalence_full_shift_full_shift_bf_size 4 ∧
    Int.natAbs Omega.bowenFranksMatrix4.det =
      pom_collision_flow_equivalence_full_shift_full_shift_bf_size 9

/-- Paper label: `cor:pom-collision-flow-equivalence-full-shift`. -/
theorem paper_pom_collision_flow_equivalence_full_shift : pom_collision_flow_equivalence_full_shift_claim := by
  have hclass := paper_pom_collision_ck_classification_q234 7
  rcases hclass with ⟨h2, h3, h4, hbf2abs, hbf3abs, hbf4abs, _, _, _, _⟩
  refine ⟨paper_pom_collision_ck_classification_q234 7, h2, h3, h4, ?_, ?_, ?_,
    hbf2abs, hbf3abs, hbf4abs⟩
  · rw [Omega.bowenFranksMatrix2_det, pom_collision_flow_equivalence_full_shift_full_shift_det]
    norm_num
  · rw [Omega.bowenFranksMatrix3_det, pom_collision_flow_equivalence_full_shift_full_shift_det]
    norm_num
  · rw [Omega.bowenFranksMatrix4_det, pom_collision_flow_equivalence_full_shift_full_shift_det]
    norm_num

end Omega.POM
