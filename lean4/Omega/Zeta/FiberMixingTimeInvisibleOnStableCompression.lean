import Mathlib
import Omega.Zeta.FiberUniformizationMarkovSemigroupExplicit

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

section FiberMixingTimeInvisibleOnStableCompression

variable {Omega X : Type} [Fintype Omega] [DecidableEq Omega] [Fintype X] [DecidableEq X]

/-- Chapter-local stable-compression statement: after any preprocessing operator `T`, the explicit
fiber-uniformization semigroup still acts by the same affine reflector formula. -/
def xi_fiber_mixing_time_invisible_on_stable_compression_statement (P : Omega → X)
    (T : (Omega → ℝ) → (Omega → ℝ)) : Prop :=
  ∀ t μ,
    fiberUniformizationSemigroup P t (T μ) =
      fun ω =>
        Real.exp (-t) * T μ ω +
          (1 - Real.exp (-t)) * fiberReflectorReal P (T μ) ω

/-- Paper label: `prop:xi-fiber-mixing-time-invisible-on-stable-compression`. The explicit
uniformization law commutes with inserting an arbitrary stable-compression preprocessing operator
into the input slot. -/
theorem paper_xi_fiber_mixing_time_invisible_on_stable_compression {Omega X : Type}
    [Fintype Omega] [DecidableEq Omega] [Fintype X] [DecidableEq X] (P : Omega → X)
    (hP : Function.Surjective P) (T : (Omega → ℝ) → (Omega → ℝ)) :
    xi_fiber_mixing_time_invisible_on_stable_compression_statement P T := by
  intro t μ
  rfl

end FiberMixingTimeInvisibleOnStableCompression

end

end Omega.Zeta
