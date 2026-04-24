import Mathlib.Tactic
import Omega.Zeta.RealInput40RotationPolytope6V

namespace Omega.Zeta

abbrev RotationPairQ := ℚ × ℚ

/-- Coordinate projection `(χ, ν, ξ) ↦ (χ, ν)`. -/
def realInput40ChiNuProjection : RotationTripleQ → RotationPairQ
  | (chi, nu, _) => (chi, nu)

/-- The projected `(χ, ν)` vertex set coming from the six explicit rotation-polytope vertices. -/
def realInput40ChiNuProjectedVertices : Finset RotationPairQ :=
  realInput40RotationVerticesChi.image realInput40ChiNuProjection

/-- The four distinct projected vertices. -/
def realInput40ChiNuQuadVertices : Finset RotationPairQ :=
  {(0, 0), ((1 : ℚ) / 2, 0), ((1 : ℚ) / 2, (1 : ℚ) / 2), (0, 1)}

/-- The projected point lying on the left edge of the quadrilateral. -/
def realInput40ChiNuEdgePoint : RotationPairQ := (0, (2 : ℚ) / 5)

/-- The projected point lying on the diagonal from `(0, 0)` to `(1/2, 1/2)`. -/
def realInput40ChiNuInteriorPoint : RotationPairQ := ((1 : ℚ) / 6, (1 : ℚ) / 6)

/-- The full six-point support obtained by projection from the explicit `(χ, ν, ξ)` vertices. -/
def realInput40ChiNuProjectedSupport : Finset RotationPairQ :=
  insert realInput40ChiNuEdgePoint (insert realInput40ChiNuInteriorPoint realInput40ChiNuQuadVertices)

/-- Region cut out by `0 ≤ χ ≤ 1/2` and `0 ≤ ν ≤ 1 - χ`. -/
def realInput40ChiNuRegion (p : RotationPairQ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ (1 : ℚ) / 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 - p.1

/-- Concrete projection of the six-vertex rotation polytope to the `(χ, ν)` plane: the projected
support consists of the four quadrilateral vertices together with two non-extreme points, each
lying in the sharp region; the two extra points are explicit convex combinations of the four
vertices, so the projected convex hull is still the same quadrilateral.
-/
def RealInput40RotationSetChiNuQuad : Prop :=
  realInput40ChiNuProjectedVertices = realInput40ChiNuProjectedSupport ∧
    (∀ p ∈ realInput40ChiNuProjectedSupport, realInput40ChiNuRegion p) ∧
    realInput40ChiNuEdgePoint =
      ((3 : ℚ) / 5) • (0, 0) + ((2 : ℚ) / 5) • (0, 1) ∧
    realInput40ChiNuInteriorPoint =
      ((2 : ℚ) / 3) • (0, 0) + ((1 : ℚ) / 3) • (((1 : ℚ) / 2), ((1 : ℚ) / 2))

/-- Projecting the six explicit `(χ, ν, ξ)` vertices to `(χ, ν)` leaves the four rational
quadrilateral vertices together with two non-extreme points already lying on the same convex hull.
    cor:real-input-40-rotation-set-chi-nu-quad -/
theorem paper_real_input_40_rotation_set_chi_nu_quad : RealInput40RotationSetChiNuQuad := by
  let _ := paper_real_input_40_rotation_polytope_6v
  refine ⟨by native_decide, ?_, by norm_num [realInput40ChiNuEdgePoint], by norm_num [realInput40ChiNuInteriorPoint]⟩
  intro p hp
  simp [realInput40ChiNuProjectedSupport, realInput40ChiNuQuadVertices, realInput40ChiNuEdgePoint,
    realInput40ChiNuInteriorPoint, realInput40ChiNuRegion] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end Omega.Zeta
