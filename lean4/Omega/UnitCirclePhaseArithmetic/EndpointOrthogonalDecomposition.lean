import Omega.Discussion.ChebyshevAdams
import Omega.UnitCirclePhaseArithmetic.ScaleLinearizationIdentityMultipliers

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing endpoint orthogonal decomposition: the discrete endpoint channel is the
`mod 4` Chebyshev-Adams residue, while the continuous endpoint scaling is recorded by the
explicit derivative multipliers at `u = ±1`.
    prop:endpoint-orthogonal-decomposition-z4-Rplus -/
theorem paper_endpoint_orthogonal_decomposition_z4_Rplus (m : ℕ) (hm : 0 < (m : ℝ)) :
    (((Omega.Discussion.chebyAdams m 0 = 0 ∨ Omega.Discussion.chebyAdams m 0 = -2 ∨
        Omega.Discussion.chebyAdams m 0 = 2) ∧
      Omega.Discussion.chebyAdams m 0 =
        match m % 4 with
        | 0 => 2
        | 1 => 0
        | 2 => -2
        | _ => 0) ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula m 1 = m ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula m (-1) = 1 / m) := by
  refine ⟨Omega.Discussion.paper_half_angle_z4_residue m, ?_⟩
  exact ⟨scalePsiDerivativeFormula_one (m : ℝ), scalePsiDerivativeFormula_neg_one hm⟩

/-- Lowercase canonical paper wrapper for
`prop:endpoint-orthogonal-decomposition-z4-Rplus`. -/
theorem paper_endpoint_orthogonal_decomposition_z4_rplus (m : ℕ) (hm : 0 < (m : ℝ)) :
    (((Omega.Discussion.chebyAdams m 0 = 0 ∨ Omega.Discussion.chebyAdams m 0 = -2 ∨
        Omega.Discussion.chebyAdams m 0 = 2) ∧
      Omega.Discussion.chebyAdams m 0 =
        match m % 4 with
        | 0 => 2
        | 1 => 0
        | 2 => -2
        | _ => 0) ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula m 1 = m ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula m (-1) = 1 / m) := by
  simpa using paper_endpoint_orthogonal_decomposition_z4_Rplus m hm

end Omega.UnitCirclePhaseArithmetic
