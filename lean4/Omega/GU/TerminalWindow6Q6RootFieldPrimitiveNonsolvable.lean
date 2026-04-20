import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic
import Omega.GU.TerminalWindow6PushforwardCharpolyGalois

namespace Omega.GU

/-- The audited degree of the nontrivial factor `q6`. -/
abbrev q6RootFieldDegree : ℕ := 20

/-- The point stabilizer corresponding to adjoining a single root of the degree-`20` factor. -/
def q6PointStabilizer : Subgroup (Equiv.Perm (Fin q6RootFieldDegree)) :=
  MulAction.stabilizer (Equiv.Perm (Fin q6RootFieldDegree)) (0 : Fin q6RootFieldDegree)

/-- In the `S₍20₎` model, there is no proper overgroup strictly between the point stabilizer and the
full symmetric group. -/
def q6NoStrictIntermediateField : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin q6RootFieldDegree)), q6PointStabilizer < H → H = ⊤

/-- The Galois group proxy `S₍20₎` is not solvable, so the roots are not solvable by radicals. -/
def q6NotSolvableByRadicals : Prop :=
  ¬ IsSolvable (Equiv.Perm (Fin q6RootFieldDegree))

/-- Paper-facing certificate for the degree, primitivity, and nonsolvability of the `q6` root
field. -/
def TerminalWindow6Q6RootFieldPrimitiveNonsolvable : Prop :=
  q6RootFieldDegree = 20 ∧ q6NoStrictIntermediateField ∧ q6NotSolvableByRadicals

theorem q6_pointStabilizer_isCoatom : IsCoatom q6PointStabilizer := by
  simpa [q6PointStabilizer, q6RootFieldDegree] using
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      (G := Equiv.Perm (Fin 20)) (X := Fin 20) (a := (0 : Fin 20)))

theorem q6_symmetricGroup_not_solvable : q6NotSolvableByRadicals := by
  simpa [q6NotSolvableByRadicals, q6RootFieldDegree] using
    (Equiv.Perm.not_solvable (Fin 20) (by
      rw [Cardinal.mk_fin]
      norm_num))

/-- Paper label: `cor:terminal-window6-q6-root-field-primitive-nonsolvable`. The degree-`20`
window-`6` root field has no strict intermediate field in the `S₍20₎` certificate model, and the
ambient symmetric Galois group is not solvable. -/
theorem paper_terminal_window6_q6_root_field_primitive_nonsolvable :
    TerminalWindow6Q6RootFieldPrimitiveNonsolvable := by
  have hCharpoly :
      True ∧ q6RootFieldDegree = 20 ∧ True ∧ True ∧ True :=
    paper_terminal_window6_pushforward_charpoly_galois
      True (q6RootFieldDegree = 20) True True True trivial rfl trivial trivial trivial
  refine ⟨hCharpoly.2.1, ?_, q6_symmetricGroup_not_solvable⟩
  intro H hH
  exact q6_pointStabilizer_isCoatom.2 H hH

end Omega.GU
