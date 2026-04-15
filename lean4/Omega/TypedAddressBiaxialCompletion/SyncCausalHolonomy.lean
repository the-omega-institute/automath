import Mathlib.Tactic

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

end Omega.TypedAddressBiaxialCompletion.SyncCausalHolonomy
