import Mathlib.Tactic
import Omega.CircleDimension.DyadicHolonomyCurvatureLimit

open Finset

namespace Omega.TypedAddressBiaxialCompletion.SyncCausalHolonomy

/-- prop:typed-address-biaxial-completion-chainwise-propagation-bound -/
theorem paper_chainwise_propagation_bound_seeds
    {n : ℕ} (dSpace tauSync : Fin n → ℝ) (cStar : ℝ)
    (hstep : ∀ i : Fin n, dSpace i ≤ cStar * tauSync i) :
    (∑ i, dSpace i) ≤ cStar * ∑ i, tauSync i := by
  calc (∑ i, dSpace i)
      ≤ ∑ i, cStar * tauSync i :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = cStar * ∑ i, tauSync i := by rw [← Finset.mul_sum]

theorem paper_chainwise_propagation_bound_package
    {n : ℕ} (dSpace tauSync : Fin n → ℝ) (cStar : ℝ)
    (hstep : ∀ i : Fin n, dSpace i ≤ cStar * tauSync i) :
    (∑ i, dSpace i) ≤ cStar * ∑ i, tauSync i :=
  paper_chainwise_propagation_bound_seeds dSpace tauSync cStar hstep

theorem paper_chainwise_propagation_bound
    {n : ℕ} (dSpace tauSync : Fin n → ℝ) (cStar : ℝ)
    (hstep : ∀ i : Fin n, dSpace i ≤ cStar * tauSync i) :
    (∑ i, dSpace i) ≤ cStar * ∑ i, tauSync i :=
  paper_chainwise_propagation_bound_seeds dSpace tauSync cStar hstep

/-- Exact typed-address paper-facing chainwise propagation wrapper.
    prop:typed-address-biaxial-completion-chainwise-propagation-bound -/
theorem paper_typed_address_biaxial_completion_chainwise_propagation_bound
    {n : ℕ} (dSpace tauSync : Fin n → ℝ) (cStar : ℝ)
    (hstep : ∀ i : Fin n, dSpace i ≤ cStar * tauSync i) :
    (∑ i, dSpace i) ≤ cStar * ∑ i, tauSync i := by
  calc (∑ i, dSpace i)
      ≤ ∑ i, cStar * tauSync i :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = cStar * ∑ i, tauSync i := by rw [← Finset.mul_sum]

end Omega.TypedAddressBiaxialCompletion.SyncCausalHolonomy

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address wrapper for the dyadic holonomy curvature limit package.
    cor:typed-address-biaxial-completion-dyadic-curvature-limit -/
theorem paper_typed_address_biaxial_completion_dyadic_curvature_limit
    (normalizedCurvatureConvergesL2 energyConverges : Prop)
    (hReconstruction : normalizedCurvatureConvergesL2 ∧ energyConverges) :
    normalizedCurvatureConvergesL2 ∧ energyConverges := by
  exact Omega.CircleDimension.paper_cdim_dyadic_holonomy_curvature_limit
    normalizedCurvatureConvergesL2 energyConverges hReconstruction

end Omega.TypedAddressBiaxialCompletion
