import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open scoped Classical

namespace Omega.POM

/-- Paper-facing finite-fiber rank/unrank package: every finite fiber is equivalent to `Fin d`,
and the standard dyadic rejection budget needs at most `Nat.clog 2 d` random bits.
    prop:pom-uniform-fiber-sampling-randomness-optimality -/
theorem paper_pom_uniform_fiber_sampling_randomness_optimality
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] (f : A → X) (x : X) :
    let d := Fintype.card {w : A // f w = x}
    ∃ e : Fin d ≃ {w : A // f w = x}, d ≤ 2 ^ Nat.clog 2 d := by
  classical
  refine ⟨(Fintype.equivFin {w : A // f w = x}).symm, ?_⟩
  by_cases hd : Fintype.card {w : A // f w = x} = 0
  · simp [hd]
  · exact Nat.le_pow_clog (by omega) _

end Omega.POM
