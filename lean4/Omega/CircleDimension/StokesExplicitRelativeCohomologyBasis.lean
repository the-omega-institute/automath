import Mathlib.Tactic
import Omega.CircleDimension.StokesExactSequenceDictionary

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- The boundary part of the pure relative Stokes model. -/
abbrev StokesPureRelativeBoundaryClass (v : ℕ) := Fin v → ℤ

/-- The relative cohomology group in the split Stokes model. -/
abbrev StokesRelativeCohomologyClass (u v : ℕ) := (Fin u → ℤ) × (Fin v → ℤ)

/-- In the pure relative case `u = 0`, the connecting map is the boundary inclusion. -/
def stokesPureRelativeConnectingMap (v : ℕ) :
    StokesPureRelativeBoundaryClass v → StokesRelativeCohomologyClass 0 v :=
  stokesBoundaryInclusion 0 v

/-- The torus-factor basis class in the split `T^u × D^v` model. -/
def stokesTorusBasisClass (u v : ℕ) (i : Fin u) : StokesRelativeCohomologyClass u v :=
  stokesSection u v (Pi.single i 1)

/-- The relative basis class coming from the boundary factor. -/
def stokesRelativeBasisClass (u v : ℕ) (j : Fin v) : StokesRelativeCohomologyClass u v :=
  stokesBoundaryInclusion u v (Pi.single j 1)

/-- Paper-facing split-coordinate statement for the explicit relative Stokes basis: the pure
relative case `u = 0` is identified with the boundary summand by the connecting map, and the
general `T^u × D^v` case is packaged by the split torus/boundary coordinates. -/
def paper_cdim_stokes_explicit_relative_cohomology_basis_statement (u v : ℕ) : Prop :=
  Function.Bijective (stokesPureRelativeConnectingMap v) ∧
    (∀ j, stokesPureRelativeConnectingMap v (Pi.single j 1) = stokesRelativeBasisClass 0 v j) ∧
    Function.Injective (stokesBoundaryInclusion u v) ∧
    Function.Surjective (stokesProjection u v) ∧
    Set.range (stokesBoundaryInclusion u v) = {p | stokesProjection u v p = 0} ∧
    (∀ p,
      stokesSection u v (stokesProjection u v p) + stokesBoundaryInclusion u v p.2 = p) ∧
    (∀ i, stokesTorusBasisClass u v i = stokesSection u v (Pi.single i 1)) ∧
    (∀ j, stokesRelativeBasisClass u v j = stokesBoundaryInclusion u v (Pi.single j 1))

private theorem stokesPureRelativeConnectingMap_surjective (v : ℕ) :
    Function.Surjective (stokesPureRelativeConnectingMap v) := by
  intro c
  refine ⟨c.2, ?_⟩
  rcases c with ⟨x, y⟩
  apply Prod.ext
  · funext i
    exact Fin.elim0 i
  · rfl

theorem paper_cdim_stokes_explicit_relative_cohomology_basis (u v : ℕ) :
    paper_cdim_stokes_explicit_relative_cohomology_basis_statement u v := by
  rcases paper_cdim_stokes_exact_sequence_dictionary u v with
    ⟨hInj, hSurj, hRange, hDecomp⟩
  refine ⟨?_, ?_, hInj, hSurj, hRange, hDecomp, ?_, ?_⟩
  · exact
      ⟨stokesBoundaryInclusion_injective 0 v, stokesPureRelativeConnectingMap_surjective v⟩
  · intro j
    rfl
  · intro i
    rfl
  · intro j
    rfl

end Omega.CircleDimension
