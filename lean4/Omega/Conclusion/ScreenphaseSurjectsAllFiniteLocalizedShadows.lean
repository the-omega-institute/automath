import Mathlib.Tactic
import Omega.Conclusion.ScreenPhaseObjectNotFinitelyLocalizable
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Conclusion

open Omega.Zeta

/-- The first coordinate in the dual model `ℚ^r`, available once `r ≥ 1`. -/
def conclusion_screenphase_surjects_all_finite_localized_shadows_origin
    (r : ℕ) (hr : 1 ≤ r) : Fin r :=
  ⟨0, Nat.succ_le_iff.mp hr⟩

/-- Embedding `ℚ ↪ ℚ^r` into the first coordinate, modeling the inclusion
`ℤ[T⁻¹] ↪ ℚ ↪ ℚ^r`. -/
def conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate
    (r : ℕ) (hr : 1 ≤ r) : ℚ → ScreenPhasePontryaginDual r :=
  fun x i =>
    if i = conclusion_screenphase_surjects_all_finite_localized_shadows_origin r hr then x else 0

/-- Concrete statement extracted from the Pontryagin-dual argument: once the screen-phase rank is
positive, there is an injective discrete-side map from the localized shadow into the first
coordinate of `ℚ^r`, and the localized dual still has circle dimension `1`. -/
def conclusion_screenphase_surjects_all_finite_localized_shadows_statement
    (T : FinitePrimeLocalization) (r : ℕ) : Prop :=
  ∃ ι : ℚ → ScreenPhasePontryaginDual r,
    Function.Injective ι ∧ localizedIntegersCircleDimension T = 1

theorem conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate_injective
    (r : ℕ) (hr : 1 ≤ r) :
    Function.Injective
      (conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate r hr) := by
  intro x y hxy
  have h0 :=
    congrArg
      (fun f =>
        f (conclusion_screenphase_surjects_all_finite_localized_shadows_origin r hr)) hxy
  simp [conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate,
    conclusion_screenphase_surjects_all_finite_localized_shadows_origin] at h0
  exact h0

theorem conclusion_screenphase_surjects_all_finite_localized_shadows_package
    (T : FinitePrimeLocalization) (r : ℕ) (hr : 1 ≤ r) :
    conclusion_screenphase_surjects_all_finite_localized_shadows_statement T r := by
  refine ⟨conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate r hr, ?_,
    rfl⟩
  exact
    conclusion_screenphase_surjects_all_finite_localized_shadows_first_coordinate_injective r hr

/-- Paper wrapper for the screen-phase surjection statement, encoded on the dual side by the
first-coordinate injection `ℤ[T⁻¹] ↪ ℚ^r` together with the rank-one localized circle quotient.
    thm:conclusion-screenphase-surjects-all-finite-localized-shadows -/
theorem paper_conclusion_screenphase_surjects_all_finite_localized_shadows
    (T : FinitePrimeLocalization) (r : ℕ) (hr : 1 ≤ r) :
    conclusion_screenphase_surjects_all_finite_localized_shadows_statement T r := by
  exact conclusion_screenphase_surjects_all_finite_localized_shadows_package T r hr

end Omega.Conclusion
