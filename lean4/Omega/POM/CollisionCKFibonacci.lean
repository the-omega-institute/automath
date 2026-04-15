import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM.CollisionCKFibonacci

/-- Cuntz parameter: C_q = F(2q-2) + 1.
    prop:pom-collision-ck-fibonacci-collapse -/
def cuntzParam (q : ℕ) : ℕ := Nat.fib (2 * q - 2) + 1

/-- Cuntz parameter seeds for q = 2..6.
    prop:pom-collision-ck-fibonacci-collapse -/
theorem cuntzParam_seeds :
    cuntzParam 2 = 2 ∧ cuntzParam 3 = 4 ∧ cuntzParam 4 = 9 ∧
    cuntzParam 5 = 22 ∧ cuntzParam 6 = 56 := by
  simp only [cuntzParam]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- F(2q-2) < F(2(q+1)-2) for q ≥ 2.
    prop:pom-collision-ck-fibonacci-collapse -/
theorem fib_even_index_strict_mono (q : ℕ) (hq : 2 ≤ q) :
    Nat.fib (2 * q - 2) < Nat.fib (2 * (q + 1) - 2) := by
  apply Nat.fib_lt_fib_succ (by omega) |>.trans_le
  exact Nat.fib_mono (by omega)

/-- Cuntz parameter is strictly monotone for q ≥ 2.
    prop:pom-collision-ck-fibonacci-collapse -/
theorem cuntzParam_strict_mono (q : ℕ) (hq : 2 ≤ q) :
    cuntzParam q < cuntzParam (q + 1) := by
  unfold cuntzParam
  exact Nat.add_lt_add_right (fib_even_index_strict_mono q hq) 1

/-- Paper package: Cuntz parameter seeds and monotonicity.
    prop:pom-collision-ck-fibonacci-collapse -/
theorem paper_pom_collision_ck_fibonacci :
    cuntzParam 2 = 2 ∧ cuntzParam 3 = 4 ∧ cuntzParam 4 = 9 ∧ cuntzParam 5 = 22 ∧
    cuntzParam 2 < cuntzParam 3 ∧ cuntzParam 3 < cuntzParam 4 ∧
    cuntzParam 4 < cuntzParam 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [cuntzParam]; native_decide

end Omega.POM.CollisionCKFibonacci
