import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega.POM.CollisionKernelDiscriminant

open Omega

/-- Characteristic polynomial of the A₂ collision kernel: x³ - 2x² - 2x + 2.
    rem:pom-residue-minpoly-a2a3a4 -/
def charPolyA2 (x : ℤ) : ℤ := x ^ 3 - 2 * x ^ 2 - 2 * x + 2

/-- Characteristic polynomial of the A₃ collision kernel: x³ - 2x² - 4x + 2.
    rem:pom-residue-minpoly-a2a3a4 -/
def charPolyA3 (x : ℤ) : ℤ := x ^ 3 - 2 * x ^ 2 - 4 * x + 2

/-- Cubic discriminant: Δ(b,c,d) = b²c² - 4c³ - 4b³d - 27d² + 18bcd
    for the monic cubic x³ + bx² + cx + d.
    rem:pom-residue-minpoly-a2a3a4 -/
def cubicDisc (b c d : ℤ) : ℤ := b ^ 2 * c ^ 2 - 4 * c ^ 3 - 4 * b ^ 3 * d - 27 * d ^ 2 + 18 * b * c * d

/-- Seed: charPolyA2(0) = 2.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem charPolyA2_zero : charPolyA2 0 = 2 := by unfold charPolyA2; ring

/-- Seed: charPolyA2(1) = -1.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem charPolyA2_one : charPolyA2 1 = -1 := by unfold charPolyA2; ring

/-- Seed: charPolyA3(0) = 2.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem charPolyA3_zero : charPolyA3 0 = 2 := by unfold charPolyA3; ring

/-- Seed: charPolyA3(1) = -3.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem charPolyA3_one : charPolyA3 1 = -3 := by unfold charPolyA3; ring

/-- Discriminant of charPolyA2 = 148.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem disc_charPolyA2 : cubicDisc (-2) (-2) 2 = 148 := by unfold cubicDisc; ring

/-- Discriminant of charPolyA3 = 564.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem disc_charPolyA3 : cubicDisc (-2) (-4) 2 = 564 := by unfold cubicDisc; ring

/-- Both discriminants are positive (real distinct roots).
    rem:pom-residue-minpoly-a2a3a4 -/
theorem disc_charPolyA2_pos : 0 < cubicDisc (-2) (-2) 2 := by
  rw [disc_charPolyA2]; norm_num

/-- Both discriminants are positive (real distinct roots).
    rem:pom-residue-minpoly-a2a3a4 -/
theorem disc_charPolyA3_pos : 0 < cubicDisc (-2) (-4) 2 := by
  rw [disc_charPolyA3]; norm_num

/-- Paper package: collision kernel characteristic polynomials and discriminants.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem paper_pom_collision_kernel_discriminant :
    charPolyA2 0 = 2 ∧ charPolyA2 1 = -1 ∧
    charPolyA3 0 = 2 ∧ charPolyA3 1 = -3 ∧
    cubicDisc (-2) (-2) 2 = 148 ∧
    cubicDisc (-2) (-4) 2 = 564 ∧
    0 < cubicDisc (-2) (-2) 2 ∧
    0 < cubicDisc (-2) (-4) 2 :=
  ⟨charPolyA2_zero, charPolyA2_one, charPolyA3_zero, charPolyA3_one,
   disc_charPolyA2, disc_charPolyA3, disc_charPolyA2_pos, disc_charPolyA3_pos⟩

/-- Trace of A₂² = 8.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem trace_collisionKernel2_sq :
    (collisionKernel2 ^ 2).trace = 8 := by native_decide

/-- Trace of A₃² = 12.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem trace_collisionKernel3_sq :
    (collisionKernel3 ^ 2).trace = 12 := by native_decide

/-- Newton identity p₂ = s₁·p₁ - 2·s₂ verification for A₂:
    tr(A₂²) = tr(A₂)² - 2·(tr(A₂)² - tr(A₂²))/2 holds as 8 = 2²−2·(−2) = 4+4 = 8.
    More precisely: tr(A²) = (tr A)² - 2·s₂ where s₂ = ((tr A)² - tr(A²))/2.
    We verify: (tr A₂)² - tr(A₂²) = 4 - 8 = -4, so s₂ = -2, and det = s₃ = -2.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem newton_A2_s2 :
    (collisionKernel2.trace ^ 2 - (collisionKernel2 ^ 2).trace) / 2 = -2 := by native_decide

/-- Newton s₂ for A₃: ((tr A₃)² - tr(A₃²))/2 = (4 - 12)/2 = -4.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem newton_A3_s2 :
    (collisionKernel3.trace ^ 2 - (collisionKernel3 ^ 2).trace) / 2 = -4 := by native_decide

/-- Paper package extended: discriminants + trace squared + Newton identities.
    rem:pom-residue-minpoly-a2a3a4 -/
theorem paper_pom_collision_kernel_full :
    cubicDisc (-2) (-2) 2 = 148 ∧
    cubicDisc (-2) (-4) 2 = 564 ∧
    (collisionKernel2 ^ 2).trace = 8 ∧
    (collisionKernel3 ^ 2).trace = 12 ∧
    (collisionKernel2.trace ^ 2 - (collisionKernel2 ^ 2).trace) / 2 = -2 ∧
    (collisionKernel3.trace ^ 2 - (collisionKernel3 ^ 2).trace) / 2 = -4 :=
  ⟨disc_charPolyA2, disc_charPolyA3,
   trace_collisionKernel2_sq, trace_collisionKernel3_sq,
   newton_A2_s2, newton_A3_s2⟩

end Omega.POM.CollisionKernelDiscriminant
