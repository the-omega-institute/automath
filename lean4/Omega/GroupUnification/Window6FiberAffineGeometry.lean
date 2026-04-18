import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GroupUnification

/-- Window-6 BinFold fibers. -/
abbrev Window6Fiber := Omega.X 6

/-- The affine-line sector of the window-6 fibers. -/
def window6AffineLineFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = true ∧ Omega.cBinFiberMult 6 x = 2)

/-- The affine-triangle sector of the window-6 fibers. -/
def window6AffineTriangleFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = true ∧ Omega.cBinFiberMult 6 x = 3)

/-- The affine-plane sector of the window-6 fibers. -/
def window6AffinePlaneFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = true ∧ Omega.cBinFiberMult 6 x = 4)

/-- The non-affine window-6 fibers. -/
def window6NonAffineFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = false)

/-- The non-affine three-point fibers. -/
def window6NonAffineThreePointFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = false ∧ Omega.cBinFiberMult 6 x = 3
  )

/-- The non-affine four-point fibers. -/
def window6NonAffineFourPointFibers : Finset Window6Fiber :=
  ((@Finset.univ Window6Fiber (Omega.fintypeX 6)).filter fun x =>
    Omega.cBinFiberIsAffine 6 x = false ∧ Omega.cBinFiberMult 6 x = 4
  )

private theorem window6_affine_geometry_counts :
    window6AffineLineFibers.card = 8 ∧
      window6AffineTriangleFibers.card = 0 ∧
      window6AffinePlaneFibers.card = 3 ∧
      window6NonAffineThreePointFibers.card = 4 ∧
      window6NonAffineFourPointFibers.card = 6 ∧
      window6NonAffineFibers.card = 10 := by
  native_decide

/-- The window-6 BinFold fibers split into eight affine lines, three affine planes, and ten
non-affine fibers; equivalently the existing `cAffineFlatCount_six` computation is the `8 + 3`
sum of the positive affine dimensions.
    thm:terminal-foldbin6-fiber-affine-geometry -/
theorem paper_terminal_foldbin6_fiber_affine_geometry :
    window6AffineLineFibers.card = 8 ∧
      window6AffineTriangleFibers.card = 0 ∧
      window6AffinePlaneFibers.card = 3 ∧
      window6NonAffineThreePointFibers.card = 4 ∧
      window6NonAffineFourPointFibers.card = 6 ∧
      window6NonAffineFibers.card = 10 ∧
      Omega.cAffineFlatCount 6 =
        window6AffineLineFibers.card + window6AffinePlaneFibers.card := by
  rcases window6_affine_geometry_counts with
    ⟨hLine, hTri, hPlane, hNonAffineThree, hNonAffineFour, hNonAffine⟩
  refine ⟨hLine, hTri, hPlane, hNonAffineThree, hNonAffineFour, hNonAffine, ?_⟩
  rw [hLine, hPlane, Omega.cAffineFlatCount_six]

end Omega.GroupUnification
