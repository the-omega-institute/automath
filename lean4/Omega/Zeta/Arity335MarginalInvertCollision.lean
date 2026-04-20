import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.Arity335CharacterEnergy

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The `c`-axis marginal of a `(3,3,5)` tensor. -/
def arity335CollisionMarginal (C : Fin 3 → Fin 3 → Fin 5 → Complex) (c : Fin 5) : Complex :=
  ∑ a, ∑ b, C a b c

/-- The pure collision coefficient recovered from the `c`-axis marginal against the explicit
`Fin 5` channel basis. -/
def arity335PureCollisionCoeff (C : Fin 3 → Fin 3 → Fin 5 → Complex) (k : Fin 5) : Complex :=
  ∑ c, arity335CollisionMarginal C c * arity335ChannelVector k c

@[simp] theorem arity335PureCollisionCoeff_eq
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) (k : Fin 5) :
    arity335PureCollisionCoeff C k = arity335CollisionMarginal C k := by
  fin_cases k <;>
    simp [arity335PureCollisionCoeff, arity335CollisionMarginal, arity335ChannelVector]

/-- Explicit `Fin 5` inversion of the collision marginal through the coordinate-channel basis. -/
def arity335MarginalInvertCollisionStatement
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) : Prop :=
  (∀ c,
    arity335CollisionMarginal C c =
      ∑ k, arity335PureCollisionCoeff C k * arity335ChannelVector k c) ∧
    (∀ k, arity335PureCollisionCoeff C k = arity335CollisionMarginal C k) ∧
    (∑ k, arity335PureCollisionCoeff C k) = ∑ c, arity335CollisionMarginal C c

/-- Summing over the two `Fin 3` axes leaves only the `c`-axis marginal, and the explicit `Fin 5`
coordinate basis recovers each pure collision coefficient from that marginal. -/
theorem arity335MarginalInvertCollisionStatement_true
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) : arity335MarginalInvertCollisionStatement C := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    fin_cases c <;>
      simp [arity335PureCollisionCoeff_eq, arity335ChannelVector]
  · intro k
    exact arity335PureCollisionCoeff_eq C k
  · simp [arity335PureCollisionCoeff_eq]

/-- Paper proposition wrapper for the `(3,3,5)` collision marginal inversion package.
    cor:arity-335-marginal-invert-collision -/
def paper_arity_335_marginal_invert_collision
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) : Prop := by
  exact arity335MarginalInvertCollisionStatement C

end

end Omega.Zeta
