import Mathlib.Tactic
import Omega.Zeta.XiTimePart9IMinimalOrientationDoubleCover

namespace Omega.Conclusion

universe u

/-- Concrete observer-orbit data with a Boolean obstruction transported along an orbit relation. -/
structure conclusion_observer_orbit_onebit_desingularization_data where
  conclusion_observer_orbit_onebit_desingularization_state : Type u
  conclusion_observer_orbit_onebit_desingularization_observer :
    conclusion_observer_orbit_onebit_desingularization_state
  conclusion_observer_orbit_onebit_desingularization_orbit :
    conclusion_observer_orbit_onebit_desingularization_state →
      conclusion_observer_orbit_onebit_desingularization_state → Prop
  conclusion_observer_orbit_onebit_desingularization_obstruction :
    conclusion_observer_orbit_onebit_desingularization_state → Bool
  conclusion_observer_orbit_onebit_desingularization_transitive :
    ∀ x : conclusion_observer_orbit_onebit_desingularization_state,
      conclusion_observer_orbit_onebit_desingularization_orbit
        conclusion_observer_orbit_onebit_desingularization_observer x
  conclusion_observer_orbit_onebit_desingularization_obstruction_invariant :
    ∀ {x y : conclusion_observer_orbit_onebit_desingularization_state},
      conclusion_observer_orbit_onebit_desingularization_orbit x y →
        conclusion_observer_orbit_onebit_desingularization_obstruction x =
          conclusion_observer_orbit_onebit_desingularization_obstruction y

/-- The external desingularization budget: zero for the trivial obstruction, one otherwise. -/
def conclusion_observer_orbit_onebit_desingularization_budget
    (D : conclusion_observer_orbit_onebit_desingularization_data) : ℕ :=
  if D.conclusion_observer_orbit_onebit_desingularization_obstruction
      D.conclusion_observer_orbit_onebit_desingularization_observer then
    1
  else
    0

namespace conclusion_observer_orbit_onebit_desingularization_data

/-- The observer orbit has exactly the zero-or-one budget dichotomy. -/
def budgetDichotomy
    (D : conclusion_observer_orbit_onebit_desingularization_data) : Prop :=
  (D.conclusion_observer_orbit_onebit_desingularization_obstruction
      D.conclusion_observer_orbit_onebit_desingularization_observer = false ∧
    conclusion_observer_orbit_onebit_desingularization_budget D = 0) ∨
    (D.conclusion_observer_orbit_onebit_desingularization_obstruction
        D.conclusion_observer_orbit_onebit_desingularization_observer = true ∧
      conclusion_observer_orbit_onebit_desingularization_budget D = 1)

end conclusion_observer_orbit_onebit_desingularization_data

/-- Paper label: `thm:conclusion-observer-orbit-onebit-desingularization`. -/
theorem paper_conclusion_observer_orbit_onebit_desingularization
    (D : conclusion_observer_orbit_onebit_desingularization_data) : D.budgetDichotomy := by
  unfold conclusion_observer_orbit_onebit_desingularization_data.budgetDichotomy
  by_cases h :
      D.conclusion_observer_orbit_onebit_desingularization_obstruction
        D.conclusion_observer_orbit_onebit_desingularization_observer = true
  · right
    exact ⟨h, by simp [conclusion_observer_orbit_onebit_desingularization_budget, h]⟩
  · left
    have hfalse :
        D.conclusion_observer_orbit_onebit_desingularization_obstruction
          D.conclusion_observer_orbit_onebit_desingularization_observer = false := by
      cases hobs :
          D.conclusion_observer_orbit_onebit_desingularization_obstruction
            D.conclusion_observer_orbit_onebit_desingularization_observer <;> simp_all
    exact
      ⟨hfalse, by
        simp [conclusion_observer_orbit_onebit_desingularization_budget, hfalse]⟩

end Omega.Conclusion
