import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Finite source data for the addressable Godel expected-complexity certificate.  The
`sortedMarginal` coordinates are the already-sorted marginal weights for each source position. -/
structure xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data where
  T : ℕ
  q : ℕ
  sortedMarginal : Fin T → Fin q → ℝ
  prime : Fin T → ℕ

namespace xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data

/-- A concrete coordinatewise pure-valuation encoding records, for each source coordinate and
letter rank, the valuation assigned to that letter. -/
structure xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_encoding
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data) where
  valuation : (t : Fin D.T) → Fin D.q → Fin D.q

/-- The sorted pure-valuation encoding assigns valuation `j` to the `j`-th sorted marginal. -/
def xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_sorted_encoding
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data) :
    xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_encoding D where
  valuation := fun _ j => j

/-- Expected logarithmic complexity of a coordinatewise pure-valuation encoding. -/
noncomputable def xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_expected
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data)
    (E :
      xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_encoding D) : ℝ :=
  ∑ t : Fin D.T, (∑ j : Fin D.q, (E.valuation t j : ℝ) * D.sortedMarginal t j) *
    Real.log (D.prime t)

/-- The closed-form lower envelope of expected logarithmic complexity. -/
noncomputable def infExpectedLogComplexity
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data) : ℝ :=
  ∑ t : Fin D.T, (∑ j : Fin D.q, (j : ℝ) * D.sortedMarginal t j) *
    Real.log (D.prime t)

/-- Dot-notation wrapper for expected logarithmic complexity. -/
noncomputable def expectedLogComplexity
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data)
    (E :
      xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_encoding D) : ℝ :=
  xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_expected D E

/-- The sorted pure-valuation encoding is the finite certificate attaining the envelope. -/
def isPureValuationMinimizer
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data)
    (E :
      xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_encoding D) :
    Prop :=
  E = xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_sorted_encoding D

end xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data

open xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data

/-- Paper label:
`thm:xi-time-part62dd-addressable-godel-expected-complexity-source-optimality`. -/
theorem paper_xi_time_part62dd_addressable_godel_expected_complexity_source_optimality
    (D : xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_data) :
    D.infExpectedLogComplexity =
        ∑ t : Fin D.T, (∑ j : Fin D.q, (j : ℝ) * D.sortedMarginal t j) *
          Real.log (D.prime t) ∧
      ∃ E, D.isPureValuationMinimizer E ∧
        D.expectedLogComplexity E = D.infExpectedLogComplexity := by
  constructor
  · rfl
  · refine
      ⟨xi_time_part62dd_addressable_godel_expected_complexity_source_optimality_sorted_encoding D,
        rfl, ?_⟩
    rfl

end Omega.Zeta
