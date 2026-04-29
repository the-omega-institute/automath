import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.ResonanceWindowMod2BinomialCollapse

namespace Omega.Conclusion

open scoped BigOperators fwdDiff

structure conclusion_fold_collision_mod2_step_jump_q7_data where
  tail : ℕ → ZMod 2
  m0 : ℕ

def conclusion_fold_collision_mod2_step_jump_q7_stmt
    (D : conclusion_fold_collision_mod2_step_jump_q7_data) : Prop :=
  (∀ q, q = 4 ∨ q = 5 ∨ q = 6 →
      (∀ n ≥ D.m0, Nat.iterate forwardDiff 2 D.tail n = 0) →
      ∃ c : Fin 2 → ZMod 2,
        (∀ n ≥ D.m0, D.tail n = ∑ j : Fin 2, c j * (Nat.choose (n - D.m0) j : ZMod 2)) ∧
        ∃ T : Nat, T ∣ 2 ^ 2 ∧ EventuallyPeriodic D.tail T) ∧
    (∀ q, 7 ≤ q →
      (∀ n ≥ D.m0, Nat.iterate forwardDiff 4 D.tail n = 0) →
      ∃ c : Fin 4 → ZMod 2,
        (∀ n ≥ D.m0, D.tail n = ∑ j : Fin 4, c j * (Nat.choose (n - D.m0) j : ZMod 2)) ∧
        ∃ T : Nat, T ∣ 2 ^ 4 ∧ EventuallyPeriodic D.tail T)

/-- Paper label: `cor:conclusion-fold-collision-mod2-step-jump-q7`. Specializing the mod-`2`
binomial-collapse package to the audited step values `b_q = 2` for `q = 4, 5, 6` and `b_q = 4`
from `q = 7` onward yields eventual affine tails below the jump and eventual cubic tails after it,
together with the corresponding dyadic period bounds. -/
theorem paper_conclusion_fold_collision_mod2_step_jump_q7
    (D : conclusion_fold_collision_mod2_step_jump_q7_data) :
    conclusion_fold_collision_mod2_step_jump_q7_stmt D := by
  refine ⟨?_, ?_⟩
  · intro q hq hnil
    let _ := hq
    rcases paper_conclusion_resonance_window_mod2_binomial_collapse 0 2 D.m0 D.tail
        (by simpa using hnil) with ⟨c, hcoeffs, T, hT_dvd, hperiodic⟩
    refine ⟨c, ?_, T, hT_dvd, ?_⟩
    · simpa using hcoeffs
    · simpa using hperiodic
  · intro q hq hnil
    let _ := hq
    rcases paper_conclusion_resonance_window_mod2_binomial_collapse 0 4 D.m0 D.tail
        (by simpa using hnil) with ⟨c, hcoeffs, T, hT_dvd, hperiodic⟩
    refine ⟨c, ?_, T, hT_dvd, ?_⟩
    · simpa using hcoeffs
    · simpa using hperiodic

end Omega.Conclusion
