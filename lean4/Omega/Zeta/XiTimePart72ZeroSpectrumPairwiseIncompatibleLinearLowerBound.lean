import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-coset data for the pairwise-incompatible zero-spectrum lower bound. -/
structure xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data where
  Point : Type
  pointDecidableEq : DecidableEq Point
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  zeroSpectrum : Finset Point
  coset : Index → Finset Point
  cosetSize : Index → ℕ
  pairwiseIncompatible :
    (↑(Finset.univ : Finset Index) : Set Index).PairwiseDisjoint coset
  cosetCard :
    ∀ i, (coset i).card = cosetSize i
  cosetSubsetZeroSpectrum :
    ∀ i, coset i ⊆ zeroSpectrum

attribute [instance]
  xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data.pointDecidableEq
  xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data.indexFintype
  xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data.indexDecidableEq

/-- The linear lower bound contributed by a disjoint family of zero cosets. -/
def xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data.linearLowerBound
    (D : xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data) : Prop :=
  ∑ i : D.Index, D.cosetSize i ≤ D.zeroSpectrum.card

/-- Paper label:
`cor:xi-time-part72-zero-spectrum-pairwise-incompatible-linear-lower-bound`. -/
theorem paper_xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound
    (D : xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data) :
    D.linearLowerBound := by
  classical
  have hUnionSubset :
      ((Finset.univ : Finset D.Index).biUnion D.coset) ⊆ D.zeroSpectrum := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨i, _hi, hxi⟩
    exact D.cosetSubsetZeroSpectrum i hxi
  have hUnionCard :
      ((Finset.univ : Finset D.Index).biUnion D.coset).card =
        ∑ i : D.Index, D.cosetSize i := by
    rw [Finset.card_biUnion D.pairwiseIncompatible]
    simp [D.cosetCard]
  rw [xi_time_part72_zero_spectrum_pairwise_incompatible_linear_lower_bound_data.linearLowerBound,
    ← hUnionCard]
  exact Finset.card_le_card hUnionSubset

end Omega.Zeta
