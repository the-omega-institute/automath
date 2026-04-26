import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.ResonanceWindowMod2BinomialCollapse

namespace Omega.Conclusion

open scoped fwdDiff

/-- Paper label: `prop:conclusion-high-collision-moment-mod2-finite-state-collapse`. This is the
paper-facing eventual-periodicity corollary extracted from the full mod-`2` binomial-collapse
package. -/
theorem paper_conclusion_high_collision_moment_mod2_finite_state_collapse
    (a b m0 : Nat) (S : Nat → ZMod 2)
    (hnil : ∀ n ≥ m0, Nat.iterate forwardDiff b (fun m => S (m + a)) n = 0) :
    ∃ T : Nat, T ∣ 2 ^ b ∧ EventuallyPeriodic (fun n => S (n + a)) T := by
  rcases paper_conclusion_resonance_window_mod2_binomial_collapse a b m0 S hnil with
    ⟨_, _, T, hT_dvd, hperiodic⟩
  exact ⟨T, hT_dvd, hperiodic⟩

end Omega.Conclusion
