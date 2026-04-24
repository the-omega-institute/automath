import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Zeta.RealInput40RotationPolytopeShear

namespace Omega.Zeta

abbrev RotationTripleQ := ℚ × ℚ × ℚ
abbrev RotationTripleR := ℝ × ℝ × ℝ

def realInput40Vertex0 : RotationTripleQ := (0, 0, 0)
def realInput40Vertex1 : RotationTripleQ := ((1 : ℚ) / 2, 0, 0)
def realInput40Vertex2 : RotationTripleQ := ((1 : ℚ) / 2, (1 : ℚ) / 2, 0)
def realInput40Vertex3 : RotationTripleQ := ((1 : ℚ) / 2, 1, (1 : ℚ) / 2)
def realInput40Vertex4 : RotationTripleQ := ((2 : ℚ) / 5, (2 : ℚ) / 5, (2 : ℚ) / 5)
def realInput40Vertex5 : RotationTripleQ := ((1 : ℚ) / 2, (1 : ℚ) / 6, (1 : ℚ) / 3)

def realInput40ChiVertex0 : RotationTripleQ := (0, 0, 0)
def realInput40ChiVertex1 : RotationTripleQ := ((1 : ℚ) / 2, 0, 0)
def realInput40ChiVertex2 : RotationTripleQ := ((1 : ℚ) / 2, (1 : ℚ) / 2, 0)
def realInput40ChiVertex3 : RotationTripleQ := (0, 1, (1 : ℚ) / 2)
def realInput40ChiVertex4 : RotationTripleQ := (0, (2 : ℚ) / 5, (2 : ℚ) / 5)
def realInput40ChiVertex5 : RotationTripleQ := ((1 : ℚ) / 6, (1 : ℚ) / 6, (1 : ℚ) / 3)

def realInput40RotationVerticesE : Finset RotationTripleQ :=
  {realInput40Vertex0, realInput40Vertex1, realInput40Vertex2, realInput40Vertex3,
    realInput40Vertex4, realInput40Vertex5}

def realInput40RotationVerticesChi : Finset RotationTripleQ :=
  {realInput40ChiVertex0, realInput40ChiVertex1, realInput40ChiVertex2, realInput40ChiVertex3,
    realInput40ChiVertex4, realInput40ChiVertex5}

/-- The shear `(e, ν, ξ) ↦ (χ, ν, ξ)` with `χ = e - ξ`, written over rationals. -/
def realInput40RotationShearQ : RotationTripleQ → RotationTripleQ
  | (e, nu, xi) => (e - xi, nu, xi)

def realInput40EFacets : RotationTripleQ → Prop
  | (e, nu, xi) =>
      0 ≤ xi ∧ xi ≤ e ∧ e ≤ (1 : ℚ) / 2 ∧ xi ≤ 2 * nu ∧
        2 * xi ≤ e + nu ∧ nu ≤ e + xi ∧ e - nu + 5 * xi ≤ 2

def realInput40ChiFacets : RotationTripleQ → Prop
  | (chi, nu, xi) =>
      0 ≤ xi ∧ 0 ≤ chi ∧ chi + xi ≤ (1 : ℚ) / 2 ∧ xi ≤ 2 * nu ∧
        xi ≤ chi + nu ∧ nu ≤ chi + 2 * xi ∧ chi - nu + 6 * xi ≤ 2

def realInput40ZeroTempSupport (thetaE thetaNu thetaXi : ℚ) : ℚ :=
  max (0 : ℚ)
    (max (((1 : ℚ) / 2) * thetaE)
      (max (((1 : ℚ) / 2) * (thetaE + thetaNu))
        (max (((1 : ℚ) / 2) * thetaE + thetaNu + ((1 : ℚ) / 2) * thetaXi)
          (max (((2 : ℚ) / 5) * (thetaE + thetaNu + thetaXi))
            (((1 : ℚ) / 2) * thetaE + ((1 : ℚ) / 6) * thetaNu + ((1 : ℚ) / 3) * thetaXi)))))

def realInput40Lift : RotationTripleQ → RotationTripleR
  | (a, b, c) => (a, b, c)

def realInput40RotESet : Set RotationTripleR :=
  fun v => ∃ q ∈ realInput40RotationVerticesE, realInput40Lift q = v

def realInput40RotChiSet : Set RotationTripleR :=
  fun v => ∃ q ∈ realInput40RotationVerticesChi, realInput40Lift q = v

private theorem realInput40RotationVerticesChi_eq_image :
    realInput40RotationVerticesChi = realInput40RotationVerticesE.image realInput40RotationShearQ := by
  native_decide

private theorem realInput40RotationVerticesE_facets :
    ∀ v ∈ realInput40RotationVerticesE, realInput40EFacets v := by
  intro v hv
  simp [realInput40RotationVerticesE, realInput40EFacets, realInput40Vertex0, realInput40Vertex1,
    realInput40Vertex2, realInput40Vertex3, realInput40Vertex4, realInput40Vertex5] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem realInput40RotationVerticesChi_facets :
    ∀ v ∈ realInput40RotationVerticesChi, realInput40ChiFacets v := by
  intro v hv
  simp [realInput40RotationVerticesChi, realInput40ChiFacets, realInput40ChiVertex0,
    realInput40ChiVertex1, realInput40ChiVertex2, realInput40ChiVertex3, realInput40ChiVertex4,
    realInput40ChiVertex5] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem realInput40RotChiSet_eq_shear_image_direct :
    realInput40RotChiSet = rotationPolytopeShear '' realInput40RotESet := by
  ext v
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [realInput40RotationVerticesChi_eq_image] at hq
    rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
    refine ⟨realInput40Lift u, ⟨u, hu, rfl⟩, ?_⟩
    rcases u with ⟨e, nu, xi⟩
    norm_num [realInput40Lift, realInput40RotationShearQ, rotationPolytopeShear]
  · rintro ⟨u, hu, rfl⟩
    rcases hu with ⟨q, hq, rfl⟩
    refine ⟨realInput40RotationShearQ q, ?_, ?_⟩
    · rw [realInput40RotationVerticesChi_eq_image]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · rcases q with ⟨e, nu, xi⟩
      norm_num [realInput40Lift, realInput40RotationShearQ, rotationPolytopeShear]

private def realInput40RotationPolytopeShearData : RealInput40RotationPolytopeShearData where
  rot_chi := realInput40RotChiSet
  shear_image_rot_e := rotationPolytopeShear '' realInput40RotESet
  support_function_pullback := True
  averageVectorShearRelation := True
  supportFunctionDotRewrite := True
  averageVectorShearRelation_h := trivial
  supportFunctionDotRewrite_h := trivial
  deriveRotationSetEquality := by
    intro _
    exact realInput40RotChiSet_eq_shear_image_direct
  deriveSupportFunctionPullback := by
    intro _ _
    trivial

/-- The explicit six rational vertices of the real-input 40-state rotation polytope, the seven
facet inequalities in both coordinate systems, the shear identification from `(e, ν, ξ)` to
`(χ, ν, ξ)`, and the zero-temperature support formula.
    thm:real-input-40-rotation-polytope-6v -/
def realInput40RotationPolytope6V : Prop :=
  realInput40RotationVerticesChi = realInput40RotationVerticesE.image realInput40RotationShearQ ∧
    (∀ v ∈ realInput40RotationVerticesE, realInput40EFacets v) ∧
    (∀ v ∈ realInput40RotationVerticesChi, realInput40ChiFacets v) ∧
    realInput40RotChiSet = rotationPolytopeShear '' realInput40RotESet ∧
    ∀ thetaE thetaNu thetaXi : ℚ,
      realInput40ZeroTempSupport thetaE thetaNu thetaXi =
        max (0 : ℚ)
          (max (((1 : ℚ) / 2) * thetaE)
            (max (((1 : ℚ) / 2) * (thetaE + thetaNu))
              (max (((1 : ℚ) / 2) * thetaE + thetaNu + ((1 : ℚ) / 2) * thetaXi)
                (max (((2 : ℚ) / 5) * (thetaE + thetaNu + thetaXi))
                  (((1 : ℚ) / 2) * thetaE + ((1 : ℚ) / 6) * thetaNu +
                    ((1 : ℚ) / 3) * thetaXi)))))

theorem paper_real_input_40_rotation_polytope_6v : realInput40RotationPolytope6V := by
  refine ⟨realInput40RotationVerticesChi_eq_image, realInput40RotationVerticesE_facets,
    realInput40RotationVerticesChi_facets,
    (paper_real_input_40_rotation_polytope_shear realInput40RotationPolytopeShearData).1, ?_⟩
  intro thetaE thetaNu thetaXi
  rfl

end Omega.Zeta
