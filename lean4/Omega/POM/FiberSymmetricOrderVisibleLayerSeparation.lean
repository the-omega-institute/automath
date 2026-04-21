import Omega.POM.FiberBirkhoffFenceIdealLattice
import Omega.POM.ToggleOrbitCountCommutantIdentity

namespace Omega.POM

/-- In the normalized fence decomposition used here, the zigzag-component multiset is represented
by the canonical component-length list itself. -/
def zigzagComponentLengthMultiset (lengths : List ℕ) : List ℕ :=
  lengths

/-- The symmetric visible layer is measured by the `q = 2` toggle commutant count. -/
def symmetricVisibleLayer (lengths : List ℕ) : ℕ :=
  toggleOrbitCount lengths 2

/-- Paper label: `thm:pom-fiber-symmetric-order-visible-layer-separation`. -/
theorem paper_pom_fiber_symmetric_order_visible_layer_separation
    (lengths_x lengths_y : List ℕ)
    (hx : ∀ n ∈ lengths_x, 2 ≤ n)
    (hy : ∀ n ∈ lengths_y, 2 ≤ n)
    (hr : lengths_x.length = lengths_y.length)
    (hsep : zigzagComponentLengthMultiset lengths_x ≠ zigzagComponentLengthMultiset lengths_y) :
    symmetricVisibleLayer lengths_x = symmetricVisibleLayer lengths_y ∧
      (⟨lengths_x⟩ : PomFiberFenceData).hasBirkhoffFenceIdealRepresentation ∧
      (⟨lengths_y⟩ : PomFiberFenceData).hasBirkhoffFenceIdealRepresentation ∧
      zigzagComponentLengthMultiset lengths_x ≠ zigzagComponentLengthMultiset lengths_y := by
  have hxSymm :
      symmetricVisibleLayer lengths_x = 2 ^ lengths_x.length := by
    simpa [symmetricVisibleLayer] using
      paper_pom_toggle_orbit_count_commutant_identity lengths_x hx
  have hySymm :
      symmetricVisibleLayer lengths_y = 2 ^ lengths_y.length := by
    simpa [symmetricVisibleLayer] using
      paper_pom_toggle_orbit_count_commutant_identity lengths_y hy
  refine ⟨?_, paper_pom_fiber_birkhoff_fence_ideal_lattice ⟨lengths_x⟩,
    paper_pom_fiber_birkhoff_fence_ideal_lattice ⟨lengths_y⟩, hsep⟩
  calc
    symmetricVisibleLayer lengths_x = 2 ^ lengths_x.length := hxSymm
    _ = 2 ^ lengths_y.length := by simp [hr]
    _ = symmetricVisibleLayer lengths_y := by simp [hySymm]

end Omega.POM
