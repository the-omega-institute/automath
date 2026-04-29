import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite certificate has two Wedderburn blocks. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_blockCount : ℕ :=
  2

/-- The scalar block in a finite Wedderburn certificate. -/
abbrev conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarBlock :=
  ℂ

/-- The first non-scalar matrix block in a finite Wedderburn certificate. -/
abbrev conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixBlock :=
  Matrix (Fin 2) (Fin 2) ℂ

/-- A concrete two-block algebra-valued channel: one scalar block and one matrix block. -/
abbrev conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra :=
  conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarBlock ×
    conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixBlock

/-- Algebra-valued Joukowsky jump law with the scalar density factor already evaluated. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_jumpLaw
    (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ) :
    Prop :=
  ext - int = c • ρ

/-- The projected scalar-block jump law. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarJump
    (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ) :
    Prop :=
  ext.1 - int.1 = c * ρ.1

/-- The projected matrix-block jump law. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixJump
    (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ) :
    Prop :=
  ext.2 - int.2 = c • ρ.2

/-- Blockwise decoupling means each Wedderburn projection satisfies its own jump law. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_blockwise
    (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ) :
    Prop :=
  conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarJump ρ ext int c ∧
    conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixJump ρ ext int c

/-- Branch exchange is central scalar multiplication on every finite matrix block. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_branchCentral : Prop :=
  (∀ z : conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarBlock,
      (-1 : ℂ) * z = -z) ∧
    ∀ A : conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixBlock,
      (-1 : ℂ) • A = -A

lemma conclusion_joukowsky_finite_group_wedderburn_decoupling_project_jumpLaw
    (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ)
    (h :
      conclusion_joukowsky_finite_group_wedderburn_decoupling_jumpLaw ρ ext int c) :
    conclusion_joukowsky_finite_group_wedderburn_decoupling_blockwise ρ ext int c := by
  constructor
  · have hscalar := congrArg Prod.fst h
    simpa [conclusion_joukowsky_finite_group_wedderburn_decoupling_jumpLaw,
      conclusion_joukowsky_finite_group_wedderburn_decoupling_scalarJump] using hscalar
  · have hmatrix := congrArg Prod.snd h
    simpa [conclusion_joukowsky_finite_group_wedderburn_decoupling_jumpLaw,
      conclusion_joukowsky_finite_group_wedderburn_decoupling_matrixJump] using hmatrix

lemma conclusion_joukowsky_finite_group_wedderburn_decoupling_branchCentral_holds :
    conclusion_joukowsky_finite_group_wedderburn_decoupling_branchCentral := by
  constructor
  · intro z
    simp
  · intro A
    ext i j
    simp

/-- Concrete statement for
`thm:conclusion-joukowsky-finite-group-wedderburn-decoupling`. -/
def conclusion_joukowsky_finite_group_wedderburn_decoupling_statement : Prop :=
  conclusion_joukowsky_finite_group_wedderburn_decoupling_blockCount = 2 ∧
    ∀ (ρ ext int : conclusion_joukowsky_finite_group_wedderburn_decoupling_algebra) (c : ℂ),
      conclusion_joukowsky_finite_group_wedderburn_decoupling_jumpLaw ρ ext int c →
        conclusion_joukowsky_finite_group_wedderburn_decoupling_blockwise ρ ext int c ∧
          conclusion_joukowsky_finite_group_wedderburn_decoupling_branchCentral

/-- Paper label: `thm:conclusion-joukowsky-finite-group-wedderburn-decoupling`. -/
theorem paper_conclusion_joukowsky_finite_group_wedderburn_decoupling :
    conclusion_joukowsky_finite_group_wedderburn_decoupling_statement := by
  refine ⟨rfl, ?_⟩
  intro ρ ext int c h
  exact ⟨conclusion_joukowsky_finite_group_wedderburn_decoupling_project_jumpLaw ρ ext int c h,
    conclusion_joukowsky_finite_group_wedderburn_decoupling_branchCentral_holds⟩

end Omega.Conclusion
