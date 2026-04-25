import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete Boolean cube used for the two-axis Euler-defect decomposition. -/
abbrev pom_euler_defect_orthogonal_pythagoras_point := Bool × Bool

/-- Real-valued observables on the Boolean cube. -/
abbrev pom_euler_defect_orthogonal_pythagoras_fn :=
  pom_euler_defect_orthogonal_pythagoras_point → ℝ

/-- First-coordinate averaging projection. -/
def pom_euler_defect_orthogonal_pythagoras_E1
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  fun x => (f (false, x.2) + f (true, x.2)) / 2

/-- Second-coordinate averaging projection. -/
def pom_euler_defect_orthogonal_pythagoras_E2
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  fun x => (f (x.1, false) + f (x.1, true)) / 2

/-- First-coordinate defect projection. -/
def pom_euler_defect_orthogonal_pythagoras_D1
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  fun x => f x - pom_euler_defect_orthogonal_pythagoras_E1 f x

/-- Second-coordinate defect projection. -/
def pom_euler_defect_orthogonal_pythagoras_D2
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  fun x => f x - pom_euler_defect_orthogonal_pythagoras_E2 f x

/-- Constant Hoeffding component. -/
def pom_euler_defect_orthogonal_pythagoras_const_component
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  pom_euler_defect_orthogonal_pythagoras_E1 (pom_euler_defect_orthogonal_pythagoras_E2 f)

/-- First-axis Hoeffding component. -/
def pom_euler_defect_orthogonal_pythagoras_axis1_component
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  pom_euler_defect_orthogonal_pythagoras_D1 (pom_euler_defect_orthogonal_pythagoras_E2 f)

/-- Second-axis Hoeffding component. -/
def pom_euler_defect_orthogonal_pythagoras_axis2_component
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  pom_euler_defect_orthogonal_pythagoras_E1 (pom_euler_defect_orthogonal_pythagoras_D2 f)

/-- Interaction Hoeffding component. -/
def pom_euler_defect_orthogonal_pythagoras_interaction_component
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_fn :=
  pom_euler_defect_orthogonal_pythagoras_D1 (pom_euler_defect_orthogonal_pythagoras_D2 f)

/-- Counting inner product on the Boolean cube. -/
def pom_euler_defect_orthogonal_pythagoras_inner
    (f g : pom_euler_defect_orthogonal_pythagoras_fn) : ℝ :=
  f (false, false) * g (false, false) +
    f (false, true) * g (false, true) +
    f (true, false) * g (true, false) +
    f (true, true) * g (true, true)

/-- Squared norm induced by the counting inner product. -/
def pom_euler_defect_orthogonal_pythagoras_norm_sq
    (f : pom_euler_defect_orthogonal_pythagoras_fn) : ℝ :=
  pom_euler_defect_orthogonal_pythagoras_inner f f

/-- Data parameter for the paper-facing theorem. The statement is uniform in the observable. -/
structure pom_euler_defect_orthogonal_pythagoras_data where

/-- Paper-facing statement: the Boolean-cube Hoeffding decomposition is exact, the four components
are pairwise orthogonal, and the counting norm satisfies the Pythagoras identity. -/
def pom_euler_defect_orthogonal_pythagoras_statement
    (_D : pom_euler_defect_orthogonal_pythagoras_data) : Prop :=
  ∀ f : pom_euler_defect_orthogonal_pythagoras_fn,
    (∀ x,
        f x =
          pom_euler_defect_orthogonal_pythagoras_const_component f x +
            pom_euler_defect_orthogonal_pythagoras_axis1_component f x +
            pom_euler_defect_orthogonal_pythagoras_axis2_component f x +
            pom_euler_defect_orthogonal_pythagoras_interaction_component f x) ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_const_component f)
          (pom_euler_defect_orthogonal_pythagoras_axis1_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_const_component f)
          (pom_euler_defect_orthogonal_pythagoras_axis2_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_const_component f)
          (pom_euler_defect_orthogonal_pythagoras_interaction_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_axis1_component f)
          (pom_euler_defect_orthogonal_pythagoras_axis2_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_axis1_component f)
          (pom_euler_defect_orthogonal_pythagoras_interaction_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_inner
          (pom_euler_defect_orthogonal_pythagoras_axis2_component f)
          (pom_euler_defect_orthogonal_pythagoras_interaction_component f) = 0 ∧
      pom_euler_defect_orthogonal_pythagoras_norm_sq f =
        pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_const_component f) +
          pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_axis1_component f) +
          pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_axis2_component f) +
          pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_interaction_component f)

/-- Paper label: `thm:pom-euler-defect-orthogonal-pythagoras`. -/
theorem paper_pom_euler_defect_orthogonal_pythagoras
    (D : pom_euler_defect_orthogonal_pythagoras_data) :
    pom_euler_defect_orthogonal_pythagoras_statement D := by
  intro f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [pom_euler_defect_orthogonal_pythagoras_const_component,
        pom_euler_defect_orthogonal_pythagoras_axis1_component,
        pom_euler_defect_orthogonal_pythagoras_axis2_component,
        pom_euler_defect_orthogonal_pythagoras_interaction_component,
        pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
        pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_const_component,
      pom_euler_defect_orthogonal_pythagoras_axis1_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_const_component,
      pom_euler_defect_orthogonal_pythagoras_axis2_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D2]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_const_component,
      pom_euler_defect_orthogonal_pythagoras_interaction_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_axis1_component,
      pom_euler_defect_orthogonal_pythagoras_axis2_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_axis1_component,
      pom_euler_defect_orthogonal_pythagoras_interaction_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_axis2_component,
      pom_euler_defect_orthogonal_pythagoras_interaction_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
    ring
  · unfold pom_euler_defect_orthogonal_pythagoras_norm_sq
      pom_euler_defect_orthogonal_pythagoras_inner
    simp [pom_euler_defect_orthogonal_pythagoras_const_component,
      pom_euler_defect_orthogonal_pythagoras_axis1_component,
      pom_euler_defect_orthogonal_pythagoras_axis2_component,
      pom_euler_defect_orthogonal_pythagoras_interaction_component,
      pom_euler_defect_orthogonal_pythagoras_E1, pom_euler_defect_orthogonal_pythagoras_E2,
      pom_euler_defect_orthogonal_pythagoras_D1, pom_euler_defect_orthogonal_pythagoras_D2]
    ring

end

end Omega.POM
