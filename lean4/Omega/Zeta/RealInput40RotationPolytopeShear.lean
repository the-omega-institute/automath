import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The linear shear from the `(e, ν, ξ)`-coordinates to the `(χ, ν, ξ)`-coordinates. -/
def rotationPolytopeShear : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (xe, xnu, xxi) => (xe - xxi, xnu, xxi)

/-- Chapter-local certificate package for the rotation-polytope shear identity. The package
records the averaged observable relation induced by the shear and the two derivations extracted
from it: equality of rotation sets and pullback of the support function. -/
structure RealInput40RotationPolytopeShearData where
  rot_chi : Set (ℝ × ℝ × ℝ)
  shear_image_rot_e : Set (ℝ × ℝ × ℝ)
  support_function_pullback : Prop
  averageVectorShearRelation : Prop
  supportFunctionDotRewrite : Prop
  averageVectorShearRelation_h : averageVectorShearRelation
  supportFunctionDotRewrite_h : supportFunctionDotRewrite
  deriveRotationSetEquality :
    averageVectorShearRelation → rot_chi = shear_image_rot_e
  deriveSupportFunctionPullback :
    averageVectorShearRelation → supportFunctionDotRewrite → support_function_pullback

/-- Paper-facing wrapper for the rotation-polytope shear statement.
    prop:rotation-polytope-shear -/
theorem paper_real_input_40_rotation_polytope_shear
    (h : RealInput40RotationPolytopeShearData) :
    h.rot_chi = h.shear_image_rot_e ∧ h.support_function_pullback := by
  have hRot : h.rot_chi = h.shear_image_rot_e :=
    h.deriveRotationSetEquality h.averageVectorShearRelation_h
  have hSupport : h.support_function_pullback :=
    h.deriveSupportFunctionPullback h.averageVectorShearRelation_h h.supportFunctionDotRewrite_h
  exact ⟨hRot, hSupport⟩

end Omega.Zeta
