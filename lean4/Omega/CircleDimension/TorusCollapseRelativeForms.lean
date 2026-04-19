import Mathlib.Tactic
import Omega.CircleDimension.StokesExactSequenceDictionary

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- Chapter-local package for the torus-collapse relative forms. The explicit forms are evaluated
on the split Stokes model `ℤ^0 × ℤ^v`, and the collapsed torus cycles are represented by the
standard basis vectors of the boundary factor. -/
structure TorusCollapseRelativeFormsData where
  torusRank : Nat
  relativeForm : Fin torusRank → ((Fin 0 → ℤ) × (Fin torusRank → ℤ)) → ℤ
  collapsedCycle : Fin torusRank → (Fin torusRank → ℤ)
  relativeForm_eq_coord : ∀ i p, relativeForm i p = p.2 i
  collapsedCycle_eq_basis : ∀ j, collapsedCycle j = Pi.single j 1

/-- In the split Stokes model for a torus-collapse fiber, one can choose explicit relative forms
dual to the collapsed torus cycles; their Kronecker pairing is the identity matrix.
    prop:cdim-torus-collapse-relative-forms -/
theorem paper_cdim_torus_collapse_relative_forms (D : TorusCollapseRelativeFormsData) :
    Function.Injective (stokesBoundaryInclusion 0 D.torusRank) ∧
      Set.range (stokesBoundaryInclusion 0 D.torusRank) =
        {p | stokesProjection 0 D.torusRank p = 0} ∧
      (∀ p,
        stokesSection 0 D.torusRank (stokesProjection 0 D.torusRank p) +
          stokesBoundaryInclusion 0 D.torusRank p.2 = p) ∧
      ∀ i j,
        D.relativeForm i
            (stokesBoundaryInclusion 0 D.torusRank (D.collapsedCycle j)) =
          if i = j then 1 else 0 := by
  rcases paper_cdim_stokes_exact_sequence_dictionary 0 D.torusRank with
    ⟨hInj, _, hRange, hDecomp⟩
  refine ⟨hInj, hRange, hDecomp, ?_⟩
  intro i j
  rw [D.relativeForm_eq_coord, D.collapsedCycle_eq_basis]
  simp [stokesBoundaryInclusion, Pi.single_apply]

end Omega.CircleDimension
