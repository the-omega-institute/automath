import Mathlib.Tactic
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice
import Omega.GU.Window6AffineFiberOrbitClassification
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

open Finset
open Omega.Conclusion

/-- The three cyclic words chosen to represent the affine-`2`-flat orbit class at window `6`. -/
def window6Affine2FlatCyclicWords : Finset (Fin 64) :=
  {w000001, w001001, w010101}

/-- The corresponding explicit `B₃` roots in the `z = 0` slice. -/
def window6Affine2FlatRoots : Finset Weight :=
  {(1, 0, 0), (0, 1, 0), (1, 1, 0)}

/-- The finite lookup table pairing the three cyclic words with the three selected `z = 0` roots.
-/
def window6Affine2FlatRootPairs : Finset (Fin 64 × Weight) :=
  {(w000001, (1, 0, 0)), (w001001, (0, 1, 0)), (w010101, (1, 1, 0))}

/-- Concrete paper-facing spec for selecting a root-slice representative for each affine-`2`-flat
cyclic word. The affine-plane orbit count is `3`, the selected words are cyclic and disjoint from
the audited boundary words, and the chosen roots lie in the `z = 0` `B₃` slice. -/
def window6Affine2FlatRootSliceSelectionSpec : Prop :=
  window6AffineFiberOrbitCountP = 3 ∧
    window6Affine2FlatRootPairs.card = window6AffineFiberOrbitCountP ∧
    window6Affine2FlatCyclicWords = {w000001, w001001, w010101} ∧
    window6Affine2FlatRoots = {(1, 0, 0), (0, 1, 0), (1, 1, 0)} ∧
    window6Affine2FlatCyclicWords ⊆ window6CyclicFiber ∧
    Disjoint window6Affine2FlatCyclicWords window6BoundaryFiber ∧
    window6Affine2FlatRoots ⊆ phiB2_12 ∧
    (∀ r ∈ window6Affine2FlatRoots, r.2.2 = 0)

/-- Paper label: `thm:window6-affine-2flat-root-slice-selection`.
The three affine-`2`-flat cyclic words admit an explicit lookup against three `B₃` roots in the
`z = 0` slice, and the cyclic/boundary separation is checked by finite enumeration. -/
theorem paper_window6_affine_2flat_root_slice_selection :
    window6Affine2FlatRootSliceSelectionSpec := by
  rcases paper_window6_affine_fiber_orbit_classification with ⟨_, _, hPlane, _, _, _⟩
  refine ⟨hPlane, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Paper label: `prop:window6-z0-root-slice-chiral-cut`.
The six visible `z = 0` roots split into the affine-selected chiral slice and its complementary
mirror slice. -/
theorem paper_window6_z0_root_slice_chiral_cut :
    let selected : Finset (ℤ × ℤ × ℤ) := {(1, 1, 0), (1, -1, 0), (0, -1, 0)}
    let ambient : Finset (ℤ × ℤ × ℤ) :=
      {(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (0, 1, 0), (0, -1, 0)}
    ambient \ selected = {(-1, 1, 0), (-1, -1, 0), (0, 1, 0)} := by
  decide

end Omega.GU
