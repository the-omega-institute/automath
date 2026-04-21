import Mathlib.Tactic
import Omega.Zeta.AppOffcriticalRadiusCompression

namespace Omega.Zeta

/-- Paper-facing horocycle/Busemann package for the off-critical Cayley point.
    cor:app-offcritical-horocycle-busemann -/
theorem paper_app_offcritical_horocycle_busemann (γ δ : ℝ) (hδ : 0 < δ) :
    appOffcriticalBoundaryDepth γ δ = Omega.Zeta.CayleyDepthIdentity.cayleyDepth δ γ 0 ∧
      appOffcriticalBoundaryDepth γ δ = δ * (4 / (γ ^ 2 + (1 + δ) ^ 2)) := by
  refine ⟨?_, ?_⟩
  · unfold appOffcriticalBoundaryDepth appOffcriticalModSq
    simpa using CayleyDepthIdentity.one_sub_cayleyModSq_eq_cayleyDepth δ γ 0 hδ
  · have hden_ne : γ ^ 2 + (1 + δ) ^ 2 ≠ 0 := by positivity
    calc
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
        exact appOffcriticalBoundaryDepth_closed_form γ δ hδ
      _ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by ring_nf
      _ = δ * (4 / (γ ^ 2 + (1 + δ) ^ 2)) := by
        field_simp [hden_ne]

end Omega.Zeta
