import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiFoldbinDyadicCapacityCriticalWindowLimit

open scoped goldenRatio

namespace Omega.Conclusion

/-- The Binet prefactor `φ² / √5` coming from `F_{m+2} / φ^m`. -/
noncomputable def binfoldCriticalCapacityBinetScale : ℝ :=
  Real.goldenRatio ^ 2 / Real.sqrt 5

/-- The conclusion-level three-phase critical-capacity law. -/
noncomputable def binfoldCriticalCapacityThreephaseLaw (ζ : ℝ) : ℝ :=
  Omega.Zeta.xiFoldbinDyadicCriticalWindowLimit ζ

/-- Rewriting the budget parameter by the Fibonacci Binet prefactor turns the dyadic critical
window theorem into the conclusion-level three-phase law with the same two breakpoints `φ⁻¹`
and `1`.
    thm:conclusion-binfold-critical-capacity-threephase-law -/
theorem paper_conclusion_binfold_critical_capacity_threephase_law :
    (∀ ζ, ζ < 1 / Real.goldenRatio →
      binfoldCriticalCapacityThreephaseLaw ζ = binfoldCriticalCapacityBinetScale * ζ) ∧
      (∀ ζ, 1 / Real.goldenRatio < ζ → ζ < 1 →
        binfoldCriticalCapacityThreephaseLaw ζ = (1 + ζ) / Real.sqrt 5) ∧
      (∀ ζ, 1 < ζ →
        binfoldCriticalCapacityThreephaseLaw ζ = 2 / Real.sqrt 5) ∧
      binfoldCriticalCapacityThreephaseLaw (1 / Real.goldenRatio) =
        Real.goldenRatio / Real.sqrt 5 ∧
      binfoldCriticalCapacityThreephaseLaw 1 = 2 / Real.sqrt 5 := by
  rcases Omega.Zeta.paper_xi_foldbin_dyadic_capacity_critical_window_limit with
    ⟨_, _, _, _, _, hlow, hmid, hhigh, hbdryPhi, hbdryOne⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    simpa [binfoldCriticalCapacityThreephaseLaw, binfoldCriticalCapacityBinetScale] using hlow ζ hζ
  · intro ζ hζ0 hζ1
    simpa [binfoldCriticalCapacityThreephaseLaw] using hmid ζ hζ0 hζ1
  · intro ζ hζ
    simpa [binfoldCriticalCapacityThreephaseLaw] using hhigh ζ hζ
  · simpa [binfoldCriticalCapacityThreephaseLaw] using hbdryPhi
  · simpa [binfoldCriticalCapacityThreephaseLaw] using hbdryOne

end Omega.Conclusion
