import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MaxentLift

namespace Omega.POM

/-- Honest log-splitting lemma for the fiber-uniform lift: the requested paper theorem needs the
numerator to be nonzero. -/
theorem pom_fiber_uniform_lift_mle_equivalence_log_split
    {X Θ : Type} [Fintype X] [DecidableEq X] (d : X → Nat) (hd : ∀ x, 0 < d x) (q : Θ → X → ℝ)
    (θ : Θ) (ω : FiberMicrostate d) (hq : q θ ω.1 ≠ 0) :
    Real.log (q θ ω.1 / d ω.1) = Real.log (q θ ω.1) - Real.log (d ω.1) := by
  have hd0 : (d ω.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hd ω.1)
  rw [Real.log_div hq hd0]

end Omega.POM
