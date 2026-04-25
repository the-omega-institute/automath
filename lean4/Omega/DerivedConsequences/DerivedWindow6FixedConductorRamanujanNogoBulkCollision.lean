import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- A nonconstant monomial supported on a finite subset of conductor coordinates. -/
structure derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial
    (Q : ℕ) where
  coeff : ℝ
  support : Finset (Fin Q)
  support_nonempty : support.Nonempty

/-- Evaluate a support-monomial on a conductor profile. -/
def derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval
    {Q : ℕ}
    (M : derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial Q)
    (z : Fin Q → ℝ) : ℝ :=
  M.coeff * ∏ q ∈ M.support, z q

/-- Concrete data encoding a fixed finite family of conductor coordinates, a finite polynomial with
zero constant term (implemented as a finite sum of nonempty-support monomials), and an unbounded
bulk collision scale. -/
structure derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data where
  conductorCount : ℕ
  monomialCount : ℕ
  coordinate : ℕ → Fin conductorCount → ℝ
  monomial :
    Fin monomialCount →
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial conductorCount
  coordinate_unit_bound : ∀ m q, |coordinate m q| ≤ 1
  bulkCollision : ℕ → ℝ
  bulk_collision_unbounded :
    ∀ B : ℝ, ∃ m : ℕ, B ≤ (Nat.fib (m + 2) : ℝ) * bulkCollision m

/-- The finite polynomial readout obtained from the fixed conductor coordinates. -/
noncomputable def derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_readout
    (D : derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data) (m : ℕ) : ℝ :=
  ∑ i, derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval
    (D.monomial i) (D.coordinate m)

/-- Sum of absolute coefficients of the finitely many nonconstant monomials. -/
noncomputable def derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum
    (D : derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data) : ℝ :=
  ∑ i, |(D.monomial i).coeff|

/-- Paper-facing statement: every fixed-conductor nonconstant polynomial readout is uniformly
bounded, hence no such readout can coincide with the unbounded bulk collision quantity
`F_{m+2} Col_m` for all `m`. -/
def derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_statement
    (D : derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data) : Prop :=
  (∀ m,
      |derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_readout D m| ≤
        derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum D) ∧
    ¬ ∀ m,
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_readout D m =
        (Nat.fib (m + 2) : ℝ) * D.bulkCollision m

private lemma derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial_bound
    (D : derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data)
    (M :
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial D.conductorCount)
    (m : ℕ) :
    |derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval M (D.coordinate m)| ≤
      |M.coeff| := by
  unfold derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval
  rw [abs_mul, Finset.abs_prod]
  have hprod_le_one :
      ∏ q ∈ M.support, |D.coordinate m q| ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro q hq
      exact abs_nonneg _
    · intro q hq
      exact D.coordinate_unit_bound m q
  exact mul_le_of_le_one_right (abs_nonneg _) hprod_le_one

/-- Paper label:
`thm:derived-window6-fixed-conductor-ramanujan-nogo-bulk-collision`. -/
theorem paper_derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision
    (derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_D :
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_data) :
    derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_statement
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_D := by
  let D := derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_D
  have hreadout :
      ∀ m,
        |derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_readout D m| ≤
          derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum D := by
    intro m
    unfold derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_readout
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum
    calc
      |∑ i,
          derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval
            (D.monomial i) (D.coordinate m)| ≤
          ∑ i,
            |derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomialEval
              (D.monomial i) (D.coordinate m)| := by
                exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(D.monomial i).coeff| := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact
              derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_monomial_bound
                D (D.monomial i) m
  refine ⟨hreadout, ?_⟩
  intro hrecovery
  let B : ℝ :=
    derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum D + 1
  rcases D.bulk_collision_unbounded B with ⟨m, hm⟩
  have hbound_m :
      (Nat.fib (m + 2) : ℝ) * D.bulkCollision m ≤
        derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum D := by
    rw [← hrecovery m]
    exact le_trans (le_abs_self _) (hreadout m)
  have : B ≤
      derived_window6_fixed_conductor_ramanujan_nogo_bulk_collision_coeffAbsSum D := le_trans hm hbound_m
  unfold B at this
  linarith

end Omega.DerivedConsequences
