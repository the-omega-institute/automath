import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.Folding.HolographicRateConservation

namespace Omega.Zeta

open Omega.Folding.HolographicRateConservation

/-- Concrete finite-fiber data for the holographic aggregation bound at one coarse concept
`\bar C`. The aggregated rate is the `-log₂` rate of the fiber weight sum, and the minimum
microscopic code length is read from the same fiber. -/
structure xi_finite_to_one_holographic_aggregation_bound_data where
  Concept : Type
  instFintypeConcept : Fintype Concept
  instDecidableEqConcept : DecidableEq Concept
  CoarseConcept : Type
  instDecidableEqCoarseConcept : DecidableEq CoarseConcept
  project : Concept → CoarseConcept
  codeLength : Concept → ℕ
  coarseConcept : CoarseConcept
  fiberBound : ℕ
  coarseConcept_nonempty : ∃ C : Concept, project C = coarseConcept
  coarseConcept_fiber_bound :
    (Finset.univ.filter fun C => project C = coarseConcept).card ≤ fiberBound
  fiberBound_pos : 1 ≤ fiberBound

attribute [instance] xi_finite_to_one_holographic_aggregation_bound_data.instFintypeConcept
attribute [instance] xi_finite_to_one_holographic_aggregation_bound_data.instDecidableEqConcept
attribute [instance]
  xi_finite_to_one_holographic_aggregation_bound_data.instDecidableEqCoarseConcept

/-- The microscopic fiber over the chosen coarse concept. -/
def xi_finite_to_one_holographic_aggregation_bound_fiber
    (D : xi_finite_to_one_holographic_aggregation_bound_data) : Finset D.Concept :=
  Finset.univ.filter fun C => D.project C = D.coarseConcept

lemma xi_finite_to_one_holographic_aggregation_bound_fiber_nonempty
    (D : xi_finite_to_one_holographic_aggregation_bound_data) :
    (xi_finite_to_one_holographic_aggregation_bound_fiber D).Nonempty := by
  rcases D.coarseConcept_nonempty with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  exact by simp [xi_finite_to_one_holographic_aggregation_bound_fiber, hC]

/-- Aggregated code length `\bar ℓ(\bar C) = -log₂ \bar w(\bar C)`. -/
noncomputable def xi_finite_to_one_holographic_aggregation_bound_aggregated_length
    (D : xi_finite_to_one_holographic_aggregation_bound_data) : ℝ :=
  mAgg (xi_finite_to_one_holographic_aggregation_bound_fiber D) (fun C => (D.codeLength C : ℝ))

/-- Minimum microscopic code length on the chosen fiber. -/
noncomputable def xi_finite_to_one_holographic_aggregation_bound_min_length
    (D : xi_finite_to_one_holographic_aggregation_bound_data) : ℝ :=
  mMin
    (xi_finite_to_one_holographic_aggregation_bound_fiber D)
    (xi_finite_to_one_holographic_aggregation_bound_fiber_nonempty D)
    (fun C => (D.codeLength C : ℝ))

/-- The aggregated code length differs from the fiber minimum by at most `log₂ M`, with the
correct orientation coming from summing the microscopic weights over the fiber. -/
def xi_finite_to_one_holographic_aggregation_bound_statement
    (D : xi_finite_to_one_holographic_aggregation_bound_data) : Prop :=
  xi_finite_to_one_holographic_aggregation_bound_min_length D -
      Real.logb 2 (D.fiberBound : ℝ) ≤
        xi_finite_to_one_holographic_aggregation_bound_aggregated_length D ∧
    xi_finite_to_one_holographic_aggregation_bound_aggregated_length D ≤
      xi_finite_to_one_holographic_aggregation_bound_min_length D

/-- Paper label: `prop:xi-finite-to-one-holographic-aggregation-bound`. -/
theorem paper_xi_finite_to_one_holographic_aggregation_bound
    (D : xi_finite_to_one_holographic_aggregation_bound_data) :
    xi_finite_to_one_holographic_aggregation_bound_statement D := by
  let S := xi_finite_to_one_holographic_aggregation_bound_fiber D
  let m : D.Concept → ℝ := fun C => (D.codeLength C : ℝ)
  have hS : S.Nonempty := xi_finite_to_one_holographic_aggregation_bound_fiber_nonempty D
  refine ⟨?_, ?_⟩
  · have hbase : mMin S hS m - Real.logb 2 (S.card : ℝ) ≤ mAgg S m :=
      mAgg_ge_mMin_sub_logb S hS m
    have hcard_pos : 0 < (S.card : ℝ) := by
      exact_mod_cast hS.card_pos
    have hbound_le : (S.card : ℝ) ≤ D.fiberBound := by
      exact_mod_cast D.coarseConcept_fiber_bound
    have hlog_le : Real.logb 2 (S.card : ℝ) ≤ Real.logb 2 (D.fiberBound : ℝ) := by
      exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcard_pos hbound_le
    dsimp [S, m] at hbase
    unfold xi_finite_to_one_holographic_aggregation_bound_min_length
      xi_finite_to_one_holographic_aggregation_bound_aggregated_length
    linarith
  · simpa [S, m, xi_finite_to_one_holographic_aggregation_bound_min_length,
      xi_finite_to_one_holographic_aggregation_bound_aggregated_length] using
      mAgg_le_mMin S hS m

end Omega.Zeta
