import Mathlib.Tactic
import Omega.Zeta.RealInput40ZetaUvCoreZpmoneResonanceSurfaces

namespace Omega.Zeta

/-- The explicit degree-`8` core polynomial in the audited `real-input-40` two-parameter model. -/
def real_input_40_det_uv_2plus8_p8 (z u v : ℤ) : ℤ :=
  realInput40UvCoreP8 z u v

/-- The explicit determinant polynomial whose factorization exhibits the `(2+8)` splitting. -/
def real_input_40_det_uv_2plus8_delta (z u v : ℤ) : ℤ :=
  (u ^ 2 * v ^ 5 - u ^ 2 * v ^ 4) * z ^ 10 +
    (-u ^ 2 * v ^ 4 - 3 * u * v ^ 4 + 3 * u * v ^ 3) * z ^ 9 +
    (3 * u * v ^ 3) * z ^ 8 +
    (2 * u ^ 2 * v ^ 3 + 7 * u * v ^ 3 - 4 * u * v ^ 2 - 2 * v ^ 3) * z ^ 7 +
    (-u ^ 2 * v ^ 3 + u ^ 2 * v ^ 2 - 3 * u * v ^ 3 - 2 * u * v ^ 2 - 6 * v ^ 3) * z ^ 6 +
    (-u ^ 2 * v ^ 2 - 5 * u * v ^ 2 + u * v + v ^ 2) * z ^ 5 +
    (4 * u * v ^ 2 - u * v + 11 * v ^ 2) * z ^ 4 +
    (u * v + 2 * v) * z ^ 3 +
    (-u * v - 6 * v) * z ^ 2 - z + 1

/-- Paper label: `thm:real-input-40-det-uv-2plus8`. -/
theorem paper_real_input_40_det_uv_2plus8 (z u v : ℤ) :
    real_input_40_det_uv_2plus8_delta z u v = (v * z ^ 2 - 1) * real_input_40_det_uv_2plus8_p8 z u v := by
  unfold real_input_40_det_uv_2plus8_delta real_input_40_det_uv_2plus8_p8 realInput40UvCoreP8
  ring

end Omega.Zeta
