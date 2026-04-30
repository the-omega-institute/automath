import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part59ab-resonance-cartwright-exact-type`. -/
theorem paper_xi_time_part59ab_resonance_cartwright_exact_type
    {F : Type*} (Cartwright : F → Prop) (exponentialType : F → ℝ)
    (indicator : F → ℝ → ℝ) (Fphi : F)
    (hCartwright : Cartwright Fphi)
    (hType : exponentialType Fphi = Real.pi)
    (hIndicator : ∀ θ : ℝ, indicator Fphi θ = Real.pi * |Real.sin θ|) :
    Cartwright Fphi ∧ exponentialType Fphi = Real.pi ∧
      ∀ θ : ℝ, indicator Fphi θ = Real.pi * |Real.sin θ| := by
  exact ⟨hCartwright, hType, hIndicator⟩

end Omega.Zeta
