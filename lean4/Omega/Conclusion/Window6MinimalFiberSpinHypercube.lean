import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The eight spin weights of the minimal window-6 fiber, encoded by three signs. -/
abbrev conclusion_window6_minimal_fiber_spin_hypercube_vertex :=
  Fin 3 → Bool

/-- The explicit equivalence with the Boolean cube model. -/
def conclusion_window6_minimal_fiber_spin_hypercube_vertex_equiv :
    conclusion_window6_minimal_fiber_spin_hypercube_vertex ≃ (Fin 3 → Bool) :=
  Equiv.refl _

/-- Hypercube adjacency: the two sign vectors differ in exactly one coordinate. -/
def conclusion_window6_minimal_fiber_spin_hypercube_adjacent
    (v w : conclusion_window6_minimal_fiber_spin_hypercube_vertex) : Prop :=
  ∃ i : Fin 3, v i ≠ w i ∧ ∀ j : Fin 3, j ≠ i → v j = w j

/-- Boundary sign action flipping the selected coordinate. -/
def conclusion_window6_minimal_fiber_spin_hypercube_boundary_action
    (i : Fin 3) (v : conclusion_window6_minimal_fiber_spin_hypercube_vertex) :
    conclusion_window6_minimal_fiber_spin_hypercube_vertex :=
  fun j => if j = i then !v j else v j

lemma conclusion_window6_minimal_fiber_spin_hypercube_boundary_action_involutive
    (i : Fin 3) :
    Function.Involutive (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action i) := by
  intro v
  funext j
  by_cases hji : j = i
  · simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action, hji]
  · simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action, hji]

lemma conclusion_window6_minimal_fiber_spin_hypercube_boundary_actions_commute
    (i j : Fin 3) (v : conclusion_window6_minimal_fiber_spin_hypercube_vertex) :
    conclusion_window6_minimal_fiber_spin_hypercube_boundary_action i
        (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action j v) =
      conclusion_window6_minimal_fiber_spin_hypercube_boundary_action j
        (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action i v) := by
  funext k
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action]
    · simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action, hkj]
  · by_cases hkj : k = j
    · subst j
      simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action, hki]
    · simp [conclusion_window6_minimal_fiber_spin_hypercube_boundary_action, hki, hkj]

/-- Paper-facing finite model of the minimal-fiber spin hypercube. -/
def conclusion_window6_minimal_fiber_spin_hypercube_statement : Prop :=
  Fintype.card conclusion_window6_minimal_fiber_spin_hypercube_vertex = 8 ∧
    Nonempty
      (conclusion_window6_minimal_fiber_spin_hypercube_vertex ≃ (Fin 3 → Bool)) ∧
    (∀ v w : conclusion_window6_minimal_fiber_spin_hypercube_vertex,
      conclusion_window6_minimal_fiber_spin_hypercube_adjacent v w ↔
        ∃ i : Fin 3, v i ≠ w i ∧ ∀ j : Fin 3, j ≠ i → v j = w j) ∧
    (∀ i : Fin 3,
      Function.Involutive (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action i)) ∧
    (∀ i j : Fin 3,
      Function.Commute
        (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action i)
        (conclusion_window6_minimal_fiber_spin_hypercube_boundary_action j))

/-- Paper label: `thm:conclusion-window6-minimal-fiber-spin-hypercube`. -/
theorem paper_conclusion_window6_minimal_fiber_spin_hypercube :
    conclusion_window6_minimal_fiber_spin_hypercube_statement := by
  refine ⟨?_, ⟨conclusion_window6_minimal_fiber_spin_hypercube_vertex_equiv⟩, ?_, ?_, ?_⟩
  · native_decide
  · intro v w
    rfl
  · intro i
    exact conclusion_window6_minimal_fiber_spin_hypercube_boundary_action_involutive i
  · intro i j v
    exact conclusion_window6_minimal_fiber_spin_hypercube_boundary_actions_commute i j v

end Omega.Conclusion
