import Mathlib.Tactic
import Omega.Zeta.XiTimeLengthCocycle
import Omega.Zeta.XiTimeFiberMinimalDimension

namespace Omega.Conclusion

open Omega.Zeta.XiTimeLengthCocycleData

/-- Paper label: `thm:conclusion-time-register-eliminability-cohomology-index-criterion`.
For the audited time-length model, triviality of the cocycle defect is equivalent to the
critical-square elimination criterion, while the minimal-dimension theorem identifies the local
index with the necessary time-register size. Therefore eliminability at size `T` is exactly the
joint condition "cohomology trivial and `B ≤ T`", and the lower-bound obstruction rules out any
smaller register. -/
theorem paper_conclusion_time_register_eliminability_cohomology_index_criterion
    {Ω X : Type*} [Fintype Ω] (Fold : Ω → X) (B T : ℕ)
    (D : Omega.Zeta.XiTimeLengthCocycleData) (critical_squares_vanish : Prop)
    (hmax : ∀ x, Nat.card (Omega.Zeta.LayerFiber Fold x) ≤ B)
    (hwit : ∃ x, Nat.card (Omega.Zeta.LayerFiber Fold x) = B)
    (hforward : critical_squares_vanish → ∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0)
    (hbackward : (∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0) → critical_squares_vanish)
    (hB : 0 < B) :
    ((Omega.Zeta.XiTimeRegisterRealization Fold T ∧ critical_squares_vanish) ↔
      (B ≤ T ∧ ∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0)) ∧
      ¬ Omega.Zeta.XiTimeRegisterRealization Fold (B - 1) := by
  have htime :=
    (Omega.Zeta.paper_xi_time_fiber_minimal_dimension Fold B T hmax hwit).1
  have hcoh : (∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0) ↔ critical_squares_vanish := by
    constructor
    · exact hbackward
    · exact hforward
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      exact ⟨htime.mp h.1, hcoh.mpr h.2⟩
    · intro h
      exact ⟨htime.mpr h.1, hcoh.mp h.2⟩
  · intro hrealize
    have hsmall :
        B ≤ B - 1 :=
      (Omega.Zeta.paper_xi_time_fiber_minimal_dimension Fold B (B - 1) hmax hwit).1.mp hrealize
    omega

end Omega.Conclusion
