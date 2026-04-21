import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit degree-`8` core factor from the audited `real-input-40` two-parameter model. -/
def realInput40UvCoreP8 (z u v : ℤ) : ℤ :=
  (u ^ 2 * v ^ 4 - u ^ 2 * v ^ 3) * z ^ 8 +
    (-u ^ 2 * v ^ 3 - 3 * u * v ^ 3 + 3 * u * v ^ 2) * z ^ 7 +
    (u ^ 2 * v ^ 3 - u ^ 2 * v ^ 2 + 3 * u * v ^ 2) * z ^ 6 +
    (u ^ 2 * v ^ 2 + 4 * u * v ^ 2 - u * v - 2 * v ^ 2) * z ^ 5 +
    (-3 * u * v ^ 2 + u * v - 6 * v ^ 2) * z ^ 4 +
    (-u * v - v) * z ^ 3 +
    (u * v + 5 * v) * z ^ 2 +
    z - 1

/-- Paper label: `thm:real-input-40-zeta-uv-core-zpmone-resonance-surfaces`. -/
theorem paper_real_input_40_zeta_uv_core_zpmone_resonance_surfaces (u v : ℤ) :
    realInput40UvCoreP8 1 u v =
        v * (u ^ 2 * v ^ 3 - u ^ 2 * v ^ 2 - 3 * u * v ^ 2 + 7 * u * v - 8 * v + 4) ∧
      realInput40UvCoreP8 (-1) u v =
        (v - 1) * (u * v - 1) * (u * v ^ 2 + 2 * u * v + 4 * v - 2) := by
  constructor <;> simp [realInput40UvCoreP8] <;> ring

end Omega.Zeta
