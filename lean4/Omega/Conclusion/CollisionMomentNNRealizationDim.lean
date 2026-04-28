import Mathlib.Tactic

namespace Omega.Conclusion

/-- Non-halting branch: the lower and upper realization bounds force dimension one. -/
theorem conclusion_collision_moment_nn_realization_dim_none_eq
    (T : Option Nat) (d : Nat) (hNone : T = none) (hNoneLower : T = none -> 1 <= d)
    (hNoneUpper : T = none -> d <= 1) : d = 1 := by
  exact le_antisymm (hNoneUpper hNone) (hNoneLower hNone)

/-- Finite halting branch: the absorbing-chain upper bound and recurrence lower bound agree. -/
theorem conclusion_collision_moment_nn_realization_dim_some_eq
    (T : Option Nat) (d t : Nat) (hSome : T = some t)
    (hSomeLower : forall t, T = some t -> t + 1 <= d)
    (hSomeUpper : forall t, T = some t -> d <= t + 1) : d = t + 1 := by
  exact le_antisymm (hSomeUpper t hSome) (hSomeLower t hSome)

/-- Paper label: `prop:conclusion-collision-moment-nn-realization-dim`. -/
theorem paper_conclusion_collision_moment_nn_realization_dim
    (q : Nat) (hq : 2 <= q) (T : Option Nat) (d : Nat)
    (hNoneLower : T = none -> 1 <= d) (hNoneUpper : T = none -> d <= 1)
    (hSomeLower : forall t, T = some t -> t + 1 <= d)
    (hSomeUpper : forall t, T = some t -> d <= t + 1) :
    (T = none -> d = 1) ∧ (forall t, T = some t -> d = t + 1) := by
  have _qWitness : 2 <= q := hq
  constructor
  · intro hNone
    exact conclusion_collision_moment_nn_realization_dim_none_eq T d hNone hNoneLower hNoneUpper
  · intro t hSome
    exact conclusion_collision_moment_nn_realization_dim_some_eq
      T d t hSome hSomeLower hSomeUpper

end Omega.Conclusion
