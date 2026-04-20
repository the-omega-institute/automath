import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- The determinant of the full depth spectrum at `t = 0`, written as the product of the depth
spectrum. -/
def xiDepthSpectrumDeterminantAtZero (a : List Real) : Real :=
  a.prod

/-- The determinant of the shadow-depth spectrum at `t = 0`, written as the product of the shadow
spectrum. -/
def xiShadowDepthSpectrumDeterminantAtZero (b : List Real) : Real :=
  b.prod

/-- The `t = 0` shadow determinant ratio. -/
noncomputable def xiShadowDeterminantRatioAtZero (Phi : Real) (a b : List Real) : Real :=
  Phi * xiShadowDepthSpectrumDeterminantAtZero b / xiDepthSpectrumDeterminantAtZero a

@[simp] theorem xiDepthSpectrumDeterminantAtZero_eq_prod (a : List Real) :
    xiDepthSpectrumDeterminantAtZero a = a.prod := by
  rfl

@[simp] theorem xiShadowDepthSpectrumDeterminantAtZero_eq_prod (b : List Real) :
    xiShadowDepthSpectrumDeterminantAtZero b = b.prod := by
  rfl

/-- Paper specialization of the determinant-ratio identity at `t = 0`. -/
theorem paper_xi_shadow_spectrum_determinant_ratio_at_zero
    (Phi : Real) (a b : List Real) :
    xiShadowDeterminantRatioAtZero Phi a b = Phi * b.prod / a.prod := by
  rfl

end Omega.Zeta
