import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppEndpointBlaschkeRadialAbsorption
import Omega.UnitCirclePhaseArithmetic.EndpointOrthogonalDecomposition
import Omega.Zeta.OffcriticalQuadraticRadialCompression
import Omega.Zeta.XiOffsetNullTypeSafety
import Omega.Zeta.XiUniqueContinuousTransverseRegister

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:xi-orthogonal-slice-structure`. The off-critical radial mode is rejected by
the unitary-slice protocol, the residual transverse register factors through the orthogonal radius,
finite Blaschke data contributes only through the endpoint absorption ledger, and the endpoint
channel itself splits into the discrete `mod 4` state and the precision ledger. -/
theorem paper_xi_orthogonal_slice_structure
    (γ δ : ℝ) (hδ : 0 < δ) {L : ℝ} {s : ℂ} (hL : 1 < L) (hs : s.re ≠ 1 / 2)
    (register : ℝ × ℝ → ℝ)
    (hphase : ∀ radius phase₁ phase₂,
      register (radius, phase₁) = register (radius, phase₂))
    (hmono : StrictMono fun radius => register (radius, 0))
    (roots : List ℂ) (m : ℕ) (hm : 0 < (m : ℝ)) :
    (appOffcriticalModSq γ δ < 1 ∧
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
      xiOffsetPwClosureNull L s ∧
      xiFactorsThroughRadius register ∧
      xiUniqueUpToMonotoneReparam register) ∧
      AppEndpointBlaschkeRadialAbsorptionStatement roots ∧
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
  have hOff := paper_xi_offcritical_quadratic_radial_compression γ δ hδ
  have hNull := paper_xi_offset_null_type_safety hL hs
  have hRegister := paper_xi_unique_continuous_transverse_register register hphase hmono
  have hInnerOuter := paper_app_endpoint_blaschke_radial_absorption roots
  have hEndpoint := paper_endpoint_orthogonal_decomposition_z4_Rplus m hm
  refine ⟨?_, hInnerOuter, hEndpoint⟩
  exact ⟨hOff.1.1, hOff.1.2.2, hNull.2.2, hRegister.1, hRegister.2⟩

end Omega.Zeta
