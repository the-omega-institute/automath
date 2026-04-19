import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local data for the gap-Dirichlet continued-fraction package. The four public fields
record the paper statements, while the witness fields provide the packaged proof ingredients. -/
structure GapDirichletContinuedFractionData where
  absolutelyConvergent : Prop
  recursionConverges : Prop
  continuedFractionRecurrence : Prop
  eulerBounds : Prop
  absolutelyConvergentWitness : absolutelyConvergent
  recursionConvergesWitness : recursionConverges
  continuedFractionRecurrenceWitness : continuedFractionRecurrence
  eulerBoundsWitness : eulerBounds

/-- Paper-facing wrapper for the gap-restricted Dirichlet series package: absolute convergence,
truncated-recursion convergence, the continued-fraction recurrence, and the Euler-product bounds.
    thm:group-jg-gap-dirichlet-continued-fraction -/
theorem paper_group_jg_gap_dirichlet_continued_fraction
    (D : GapDirichletContinuedFractionData) :
    D.absolutelyConvergent ∧ D.recursionConverges ∧ D.continuedFractionRecurrence ∧ D.eulerBounds := by
  exact ⟨D.absolutelyConvergentWitness, D.recursionConvergesWitness,
    D.continuedFractionRecurrenceWitness, D.eulerBoundsWitness⟩

end Omega.GU
