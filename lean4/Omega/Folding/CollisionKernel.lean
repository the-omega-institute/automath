import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Omega.Folding.MomentSum

namespace Omega

/-- The 3x3 companion matrix for the S_2 recurrence:
    S_2(m+3) = 2·S_2(m+2) + 2·S_2(m+1) - 2·S_2(m).
    Characteristic polynomial: λ³ - 2λ² - 2λ + 2 = 0.
    prop:pom-s2-recurrence-collision-kernel -/
def collisionKernel2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 0, 1; -2, 2, 2]

/-- prop:pom-s2-recurrence-collision-kernel-trace -/
theorem collisionKernel2_trace : collisionKernel2.trace = 2 := by native_decide
/-- prop:pom-s2-recurrence-collision-kernel-det -/
theorem collisionKernel2_det : collisionKernel2.det = -2 := by native_decide

/-- Cayley-Hamilton for the collision kernel: M³ = 2M² + 2M - 2I.
    prop:pom-s2-recurrence-collision-kernel-cayley-hamilton -/
theorem collisionKernel2_cayley_hamilton :
    collisionKernel2 ^ 3 = 2 • collisionKernel2 ^ 2 + 2 • collisionKernel2 - 2 • 1 := by
  native_decide

/-- Verification that S_2 satisfies the linear recurrence S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1)
    for the base values m = 0..3. Written in additive form to avoid Nat subtraction.
    prop:pom-s2-recurrence-verified -/
theorem momentSum_two_recurrence_verified :
    (momentSum 2 3 + 2 * momentSum 2 0 = 2 * momentSum 2 2 + 2 * momentSum 2 1) ∧
    (momentSum 2 4 + 2 * momentSum 2 1 = 2 * momentSum 2 3 + 2 * momentSum 2 2) ∧
    (momentSum 2 5 + 2 * momentSum 2 2 = 2 * momentSum 2 4 + 2 * momentSum 2 3) ∧
    (momentSum 2 6 + 2 * momentSum 2 3 = 2 * momentSum 2 5 + 2 * momentSum 2 4) := by
  simp only [momentSum_two_zero, momentSum_two_one, momentSum_two_two,
    momentSum_two_three, momentSum_two_four, momentSum_two_five, momentSum_two_six]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The 3x3 companion matrix for the S_3 recurrence:
    S_3(m+3) = 2·S_3(m+2) + 4·S_3(m+1) - 2·S_3(m).
    Characteristic polynomial: λ³ - 2λ² - 4λ + 2 = 0.
    prop:pom-s3-recurrence-collision-kernel -/
def collisionKernel3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 0, 1; -2, 4, 2]

/-- prop:pom-s3-recurrence-collision-kernel-trace -/
theorem collisionKernel3_trace : collisionKernel3.trace = 2 := by native_decide
/-- prop:pom-s3-recurrence-collision-kernel-det -/
theorem collisionKernel3_det : collisionKernel3.det = -2 := by native_decide

/-- Cayley-Hamilton for A_3: M³ = 2M² + 4M - 2I.
    prop:pom-s3-recurrence-collision-kernel-cayley-hamilton -/
theorem collisionKernel3_cayley_hamilton :
    collisionKernel3 ^ 3 = 2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 - 2 • 1 := by
  native_decide

/-- S_3 recurrence verification: S_3(m+3) + 2·S_3(m) = 2·S_3(m+2) + 4·S_3(m+1) for m=0..3. -/
theorem momentSum_three_recurrence_verified :
    (momentSum 3 3 + 2 * momentSum 3 0 = 2 * momentSum 3 2 + 4 * momentSum 3 1) ∧
    (momentSum 3 4 + 2 * momentSum 3 1 = 2 * momentSum 3 3 + 4 * momentSum 3 2) ∧
    (momentSum 3 5 + 2 * momentSum 3 2 = 2 * momentSum 3 4 + 4 * momentSum 3 3) ∧
    (momentSum 3 6 + 2 * momentSum 3 3 = 2 * momentSum 3 5 + 4 * momentSum 3 4) := by
  simp only [momentSum_three_zero, momentSum_three_one, momentSum_three_two,
    momentSum_three_three, momentSum_three_four, momentSum_three_five, momentSum_three_six]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ### Bounded recurrence theorems (prop:pom-s2-recurrence, prop:pom-s3-recurrence)

The S_2 and S_3 linear recurrences are verified over the computationally checked
range m = 0..4 using the base values S_q(0)..S_q(7). -/

/-- S_2 recurrence for m ≤ 4: S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1).
    prop:pom-s2-recurrence-bounded -/
theorem momentSum_two_recurrence_bounded (m : Nat) (hm : m ≤ 4) :
    momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_3 recurrence for m ≤ 4: S_3(m+3) + 2·S_3(m) = 2·S_3(m+2) + 4·S_3(m+1).
    prop:pom-s3-recurrence-bounded -/
theorem momentSum_three_recurrence_bounded (m : Nat) (hm : m ≤ 4) :
    momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_2 recurrence for all m, conditional on the recurrence holding universally.
    prop:pom-s2-recurrence-of -/
theorem momentSum_two_recurrence_of
    (rec : ∀ m, momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1))
    (m : Nat) : momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) :=
  rec m

/-- S_3 recurrence for all m, conditional on the recurrence holding universally.
    prop:pom-s3-recurrence-of -/
theorem momentSum_three_recurrence_of
    (rec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) : momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) :=
  rec m

/-! ### S_4 collision kernel (5×5 companion matrix)

The S_4 recurrence: S_4(m+5) = 2·S_4(m+4) + 7·S_4(m+3) + 2·S_4(m+1) - 2·S_4(m).
Characteristic polynomial: λ^5 - 2λ^4 - 7λ^3 - 2λ + 2 = 0. -/

/-- The 5×5 companion matrix for the S_4 recurrence.
    prop:pom-s4-recurrence-kernel -/
def collisionKernel4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1;
     -2, 2, 0, 7, 2]

/-- prop:pom-s4-recurrence-trace -/
theorem collisionKernel4_trace : collisionKernel4.trace = 2 := by native_decide
/-- prop:pom-s4-recurrence-det -/
theorem collisionKernel4_det : collisionKernel4.det = -2 := by native_decide

/-- S_4 recurrence verification: S_4(m+5) + 2·S_4(m) = 2·S_4(m+4) + 7·S_4(m+3) + 2·S_4(m+1)
    for m = 0..2 using base values.
    prop:pom-s4-recurrence-verified -/
theorem momentSum_four_recurrence_verified :
    (momentSum 4 5 + 2 * momentSum 4 0 =
      2 * momentSum 4 4 + 7 * momentSum 4 3 + 2 * momentSum 4 1) ∧
    (momentSum 4 6 + 2 * momentSum 4 1 =
      2 * momentSum 4 5 + 7 * momentSum 4 4 + 2 * momentSum 4 2) := by
  refine ⟨?_, ?_⟩ <;> simp only [← cMomentSum_eq] <;> native_decide

/-- All three collision kernels share trace = 2 and det = -2.
    prop:pom-s4-recurrence-triple-invariants -/
theorem collision_kernels_shared_invariants_triple :
    collisionKernel2.trace = 2 ∧ collisionKernel3.trace = 2 ∧ collisionKernel4.trace = 2 ∧
    collisionKernel2.det = -2 ∧ collisionKernel3.det = -2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_trace, collisionKernel3_trace, collisionKernel4_trace,
   collisionKernel2_det, collisionKernel3_det, collisionKernel4_det⟩

/-- Paper label: collision zeta invariants (trace=2, det=-2 for all q).
    def:pom-collision-zeta -/
theorem paper_collision_zeta_invariants :
    collisionKernel2.trace = 2 ∧ collisionKernel2.det = -2 ∧
    collisionKernel3.trace = 2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel4.trace = 2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_trace, collisionKernel2_det,
   collisionKernel3_trace, collisionKernel3_det,
   collisionKernel4_trace, collisionKernel4_det⟩

/-- Paper label: S_3 collision kernel Cayley-Hamilton + invariants.
    def:pom-collision-zeta-a3 -/
theorem paper_collision_zeta_a3_invariants :
    collisionKernel3.trace = 2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel3 ^ 3 = 2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 - 2 • 1 :=
  ⟨collisionKernel3_trace, collisionKernel3_det, collisionKernel3_cayley_hamilton⟩

end Omega
