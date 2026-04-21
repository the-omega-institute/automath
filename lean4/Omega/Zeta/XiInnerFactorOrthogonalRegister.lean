import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiOrthogonalSliceStructure

namespace Omega.Zeta

/-- Direct corollary of the orthogonal slice package for a concrete radial register: phase-only
readout does not distinguish the two probe points, while the orthogonal radial register does and
all off-critical/endpoint bookkeeping factors through that extra channel. -/
def xi_inner_factor_orthogonal_register_statement : Prop :=
  let register : ℝ × ℝ → ℝ := fun u => u.1
  xiPhaseProjection (0, 0) = xiPhaseProjection (1, 0) ∧
    register (0, 0) ≠ register (1, 0) ∧
    xiOffsetPwClosureNull 2 0 ∧
    xiFactorsThroughRadius register ∧
    xiUniqueUpToMonotoneReparam register ∧
    Omega.UnitCirclePhaseArithmetic.AppEndpointBlaschkeRadialAbsorptionStatement ([] : List ℂ) ∧
    (((Omega.Discussion.chebyAdams 1 0 = 0 ∨ Omega.Discussion.chebyAdams 1 0 = -2 ∨
        Omega.Discussion.chebyAdams 1 0 = 2) ∧
      Omega.Discussion.chebyAdams 1 0 =
        match 1 % 4 with
        | 0 => 2
        | 1 => 0
        | 2 => -2
        | _ => 0) ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula (1 : ℝ) 1 = 1 ∧
      Omega.UnitCirclePhaseArithmetic.scalePsiDerivativeFormula (1 : ℝ) (-1) = 1)

theorem paper_xi_inner_factor_orthogonal_register :
    xi_inner_factor_orthogonal_register_statement := by
  dsimp [xi_inner_factor_orthogonal_register_statement]
  have hSlice :=
    paper_xi_orthogonal_slice_structure
      (γ := 0) (δ := 1) (hδ := by norm_num) (L := 2) (s := 0)
      (register := fun u : ℝ × ℝ => u.1)
      (hphase := by intro radius phase₁ phase₂; rfl)
      (hmono := by
        intro a b hab
        simpa using hab)
      (roots := []) (m := 1) (hm := by norm_num)
      (hL := by norm_num) (hs := by norm_num)
  rcases hSlice with ⟨hMain, hEndpoint, hOrthogonal⟩
  rcases hMain with ⟨_, _, hNull, hFactor, hUnique⟩
  refine ⟨by simp [xiPhaseProjection], by simp, hNull, hFactor, hUnique, hEndpoint, ?_⟩
  simpa using hOrthogonal

end Omega.Zeta
