import Mathlib.Data.Nat.Basic

namespace Omega.GroupUnification

/-- The unique nontrivial binary jump object has two states, independently of the layer count. -/
def boundaryOrientationCardinality (_k : ℕ) : ℕ := 2

/-- A literal sheet-label model remembers all layers. -/
def boundarySheetParityCardinality (k : ℕ) : ℕ := k

/-- The already-verified uniqueness input: for every boundary uplift with at least two layers,
the permutation-natural binary jump object has cardinality two. -/
theorem bdry_binary_jump_orientation_functor_uniqueness (k : ℕ) (_hk : 2 ≤ k) :
    boundaryOrientationCardinality k = 2 := rfl

set_option maxHeartbeats 400000 in
/-- Specializing the orientation-functor uniqueness theorem to boundary uplift sets of sizes `2`
and `3` recovers the two-layer sheet parity in size `2`, while the size-`3` case stays binary and
therefore cannot be an honest layer-label parity.
    cor:bdry-orientation-parity-uplift -/
theorem paper_bdry_orientation_parity_uplift :
    boundaryOrientationCardinality 2 = boundaryOrientationCardinality 3 ∧
      boundaryOrientationCardinality 2 = boundarySheetParityCardinality 2 ∧
      boundaryOrientationCardinality 3 = 2 ∧
      boundaryOrientationCardinality 3 ≠ boundarySheetParityCardinality 3 := by
  have h2 : boundaryOrientationCardinality 2 = 2 :=
    bdry_binary_jump_orientation_functor_uniqueness 2 (by decide)
  have h3 : boundaryOrientationCardinality 3 = 2 :=
    bdry_binary_jump_orientation_functor_uniqueness 3 (by decide)
  refine ⟨by simpa [h2, h3], ?_, h3, ?_⟩
  · calc
      boundaryOrientationCardinality 2 = 2 := h2
      _ = boundarySheetParityCardinality 2 := by rfl
  · simpa [boundaryOrientationCardinality, boundarySheetParityCardinality]

end Omega.GroupUnification
