import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The audited window-6 fiber multiplicity support. -/
def xi_time_part9ze_window6_bit_ladder_fiberMultiplicitySet : Finset ℕ :=
  {2, 3, 4}

/-- Dyadic lift attached to a finite index. -/
def xi_time_part9ze_window6_bit_ladder_dyadicLift (n : ℕ) : ℕ :=
  2 ^ n

/-- Integer dyadic cost, i.e. the base-2 logarithmic cost rounded down. -/
def xi_time_part9ze_window6_bit_ladder_dyadicCost (n : ℕ) : ℕ :=
  Nat.log 2 n

/-- Concrete data for the three window-6 conditional-expectation index identities. -/
structure xi_time_part9ze_window6_bit_ladder_data where
  xi_time_part9ze_window6_bit_ladder_indexEZ : ℕ
  xi_time_part9ze_window6_bit_ladder_indexEpsilon : ℕ
  xi_time_part9ze_window6_bit_ladder_indexEsc : ℕ
  xi_time_part9ze_window6_bit_ladder_indexEZ_identity :
    xi_time_part9ze_window6_bit_ladder_indexEZ = 4
  xi_time_part9ze_window6_bit_ladder_indexEpsilon_identity :
    xi_time_part9ze_window6_bit_ladder_indexEpsilon = 32
  xi_time_part9ze_window6_bit_ladder_indexEsc_identity :
    xi_time_part9ze_window6_bit_ladder_indexEsc = 64

namespace xi_time_part9ze_window6_bit_ladder_data

/-- The three dyadic log identities and the finite worst-case cost over the audited support
`{2,3,4}`. -/
def statement (D : xi_time_part9ze_window6_bit_ladder_data) : Prop :=
  xi_time_part9ze_window6_bit_ladder_dyadicCost
      D.xi_time_part9ze_window6_bit_ladder_indexEZ = 2 ∧
    xi_time_part9ze_window6_bit_ladder_dyadicCost
        D.xi_time_part9ze_window6_bit_ladder_indexEpsilon = 5 ∧
      xi_time_part9ze_window6_bit_ladder_dyadicCost
          D.xi_time_part9ze_window6_bit_ladder_indexEsc = 6 ∧
        (∀ n ∈ xi_time_part9ze_window6_bit_ladder_fiberMultiplicitySet,
          6 - xi_time_part9ze_window6_bit_ladder_dyadicCost n ≤ 5) ∧
          (∃ n ∈ xi_time_part9ze_window6_bit_ladder_fiberMultiplicitySet,
            6 - xi_time_part9ze_window6_bit_ladder_dyadicCost n = 5)

end xi_time_part9ze_window6_bit_ladder_data

/-- Paper label: `cor:xi-time-part9ze-window6-bit-ladder`. -/
theorem paper_xi_time_part9ze_window6_bit_ladder
    (D : xi_time_part9ze_window6_bit_ladder_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [D.xi_time_part9ze_window6_bit_ladder_indexEZ_identity]
    native_decide
  · rw [D.xi_time_part9ze_window6_bit_ladder_indexEpsilon_identity]
    native_decide
  · rw [D.xi_time_part9ze_window6_bit_ladder_indexEsc_identity]
    native_decide
  · native_decide
  · exact ⟨2, by native_decide, by native_decide⟩

end Omega.Zeta
