import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.GU.GodelLorentzAlgebraization

namespace Omega.GU

/-- Paper label: `cor:group-jg-ellipse-area-ellipsoid-gap`. The Joukowsky ellipse with semiaxes
`a = √L + 1 / √L` and `b = √L - 1 / √L` has area `π (L - L⁻¹)`. -/
theorem paper_group_jg_ellipse_area_ellipsoid_gap (L : ℝ) (hL : 1 < L) :
    let r := Real.sqrt L
    let a := r + r⁻¹
    let b := r - r⁻¹
    Real.pi * a * b = Real.pi * (L - L⁻¹) := by
  dsimp
  have hL_pos : 0 < L := lt_trans zero_lt_one hL
  have hsqrt_ne : (Real.sqrt L : ℝ) ≠ 0 := by positivity
  have hmain :
      (Real.sqrt L + (Real.sqrt L)⁻¹) * (Real.sqrt L - (Real.sqrt L)⁻¹) = L - L⁻¹ := by
    field_simp [hsqrt_ne, ne_of_gt hL_pos]
    rw [Real.sq_sqrt hL_pos.le]
    ring
  calc
    Real.pi * (Real.sqrt L + (Real.sqrt L)⁻¹) * (Real.sqrt L - (Real.sqrt L)⁻¹)
        = Real.pi * ((Real.sqrt L + (Real.sqrt L)⁻¹) * (Real.sqrt L - (Real.sqrt L)⁻¹)) := by
            ring
    _ = Real.pi * (L - L⁻¹) := by rw [hmain]

end Omega.GU
