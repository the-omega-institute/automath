import Omega.Folding.BoundaryLayer

namespace Omega.GroupUnification

/-- A concrete parity readout on the unordered three-sheet boundary fiber appearing at `m = 7`.
The fiber is modeled by `Fin 3`, with `S₃` acting through permutations. -/
structure BdrySheetParityExtensionData where
  parityReadout : Fin 3 → Fin 2

namespace BdrySheetParityExtensionData

/-- The parity readout depends only on the unordered three-sheet fiber, so it is invariant under
every permutation of the sheets. -/
def permutationInvariant (D : BdrySheetParityExtensionData) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), ∀ x : Fin 3, D.parityReadout (σ x) = D.parityReadout x

/-- At `m = 7`, permutation invariance forces the parity readout to be constant across the whole
three-sheet fiber. -/
def parityAtM7Trivial (D : BdrySheetParityExtensionData) : Prop :=
  ∀ x y : Fin 3, D.parityReadout x = D.parityReadout y

end BdrySheetParityExtensionData

open BdrySheetParityExtensionData

/-- A permutation-invariant `ℤ₂`-grading on the unordered three-sheet boundary fiber cannot
distinguish a `1 ⊔ 2` split, so the only possible grading at `m = 7` is the trivial one.
    prop:bdry-sheet-parity-extension-obstruction-m7 -/
theorem paper_bdry_sheet_parity_extension_obstruction_m7 (D : BdrySheetParityExtensionData) :
    D.permutationInvariant -> D.parityAtM7Trivial := by
  intro hperm
  exact Omega.no_nontrivial_sym_invariant_grading_fin3 D.parityReadout hperm

end Omega.GroupUnification
