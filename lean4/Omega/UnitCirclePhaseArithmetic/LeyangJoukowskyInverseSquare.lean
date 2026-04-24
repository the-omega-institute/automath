import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:jouwkowsky-inverse-square`. -/
theorem paper_leyang_jouwkowsky_inverse_square (z : Complex) (hz : z ≠ 0) :
    -z ^ 2 / (1 + z ^ 2) ^ 2 = -(1 / (z + 1 / z) ^ 2) := by
  by_cases hsing : 1 + z ^ 2 = 0
  · have htrace : z + 1 / z = 0 := by
      have hmul : z * (z + 1 / z) = 0 := by
        calc
          z * (z + 1 / z) = z ^ 2 + 1 := by
            field_simp [hz]
          _ = 0 := by simpa [add_comm] using hsing
      exact (mul_eq_zero.mp hmul).resolve_left hz
    have htrace' : z + z⁻¹ = 0 := by
      simpa [one_div] using htrace
    simp [hsing, htrace']
  · field_simp [hz, hsing]
    rw [show z ^ 2 + 1 = 1 + z ^ 2 by ring]
    field_simp [hsing]

end Omega.UnitCirclePhaseArithmetic
