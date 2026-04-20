import Mathlib.Tactic
import Omega.POM.FenceMobiusRigidity

namespace Omega.POM

open scoped BigOperators

/-- The chapter-local single-parameter audit is exactly the nonvanishing branch of the existing
fence-interval Möbius rigidity statement. -/
theorem paper_pom_fiber_boolean_interval_single_parameter_audit (lengths : List Nat)
    (I J : FenceIdealProfile lengths) (hIJ : ∀ i, I i ≤ J i) :
    let q := ∑ i, ((J i : Nat) - I i)
    (∀ i, J i - I i ≤ 1) → fenceIntervalMobius lengths I J = (-1 : Int) ^ q := by
  dsimp
  let _ := hIJ
  intro hBoolean
  simp [fenceIntervalMobius, hBoolean]

end Omega.POM
