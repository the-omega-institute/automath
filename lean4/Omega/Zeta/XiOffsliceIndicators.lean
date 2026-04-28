import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite off-slice Blaschke-zero ledger for
`thm:xi-offslice-indicators-additivity`. -/
structure xi_offslice_indicators_additivity_data where
  xi_offslice_indicators_additivity_Zero : Type
  xi_offslice_indicators_additivity_fintype :
    Fintype xi_offslice_indicators_additivity_Zero
  xi_offslice_indicators_additivity_decidableEq :
    DecidableEq xi_offslice_indicators_additivity_Zero
  xi_offslice_indicators_additivity_leftZeros : Finset xi_offslice_indicators_additivity_Zero
  xi_offslice_indicators_additivity_rightZeros : Finset xi_offslice_indicators_additivity_Zero
  xi_offslice_indicators_additivity_disjointZeros :
    Disjoint xi_offslice_indicators_additivity_leftZeros
      xi_offslice_indicators_additivity_rightZeros
  xi_offslice_indicators_additivity_weight :
    xi_offslice_indicators_additivity_Zero → ℝ
  xi_offslice_indicators_additivity_originModulus : Finset xi_offslice_indicators_additivity_Zero → ℝ
  xi_offslice_indicators_additivity_originProduct :
    xi_offslice_indicators_additivity_originModulus
        (xi_offslice_indicators_additivity_leftZeros ∪
          xi_offslice_indicators_additivity_rightZeros) =
      xi_offslice_indicators_additivity_originModulus
          xi_offslice_indicators_additivity_leftZeros *
        xi_offslice_indicators_additivity_originModulus
          xi_offslice_indicators_additivity_rightZeros

attribute [instance]
  xi_offslice_indicators_additivity_data.xi_offslice_indicators_additivity_fintype
  xi_offslice_indicators_additivity_data.xi_offslice_indicators_additivity_decidableEq

namespace xi_offslice_indicators_additivity_data

/-- The residual indicator is the number of off-slice zeros, counted in the finite ledger. -/
def indicator (D : xi_offslice_indicators_additivity_data)
    (S : Finset D.xi_offslice_indicators_additivity_Zero) : ℕ :=
  S.card

/-- The additive weight functional on an off-slice zero ledger. -/
def weightFunctional (D : xi_offslice_indicators_additivity_data)
    (S : Finset D.xi_offslice_indicators_additivity_Zero) : ℝ :=
  ∑ z ∈ S, D.xi_offslice_indicators_additivity_weight z

/-- Disjoint products add their residual indicators. -/
def indicatorAdditive (D : xi_offslice_indicators_additivity_data) : Prop :=
  D.indicator
      (D.xi_offslice_indicators_additivity_leftZeros ∪
        D.xi_offslice_indicators_additivity_rightZeros) =
    D.indicator D.xi_offslice_indicators_additivity_leftZeros +
      D.indicator D.xi_offslice_indicators_additivity_rightZeros

/-- Disjoint products add their weighted zero counts. -/
def weightAdditive (D : xi_offslice_indicators_additivity_data) : Prop :=
  D.weightFunctional
      (D.xi_offslice_indicators_additivity_leftZeros ∪
        D.xi_offslice_indicators_additivity_rightZeros) =
    D.weightFunctional D.xi_offslice_indicators_additivity_leftZeros +
      D.weightFunctional D.xi_offslice_indicators_additivity_rightZeros

/-- Evaluation at the origin is multiplicative for the chosen finite Blaschke factorization. -/
def originModulusMultiplicative (D : xi_offslice_indicators_additivity_data) : Prop :=
  D.xi_offslice_indicators_additivity_originModulus
      (D.xi_offslice_indicators_additivity_leftZeros ∪
        D.xi_offslice_indicators_additivity_rightZeros) =
    D.xi_offslice_indicators_additivity_originModulus
        D.xi_offslice_indicators_additivity_leftZeros *
      D.xi_offslice_indicators_additivity_originModulus
        D.xi_offslice_indicators_additivity_rightZeros

end xi_offslice_indicators_additivity_data

open xi_offslice_indicators_additivity_data

/-- Paper label: `thm:xi-offslice-indicators-additivity`. -/
theorem paper_xi_offslice_indicators_additivity (D : xi_offslice_indicators_additivity_data) :
    D.indicatorAdditive ∧ D.weightAdditive ∧ D.originModulusMultiplicative := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [indicatorAdditive, indicator, Finset.card_union_of_disjoint,
      D.xi_offslice_indicators_additivity_disjointZeros]
  · simp [weightAdditive, weightFunctional, Finset.sum_union,
      D.xi_offslice_indicators_additivity_disjointZeros]
  · exact D.xi_offslice_indicators_additivity_originProduct

/-- Concrete fixed-slice zero ledger for
`prop:xi-offslice-fixed-slice-indicator-criterion`. -/
structure xi_offslice_fixed_slice_indicator_criterion_data where
  xi_offslice_fixed_slice_indicator_criterion_Zero : Type
  xi_offslice_fixed_slice_indicator_criterion_fintype :
    Fintype xi_offslice_fixed_slice_indicator_criterion_Zero
  xi_offslice_fixed_slice_indicator_criterion_decidableEq :
    DecidableEq xi_offslice_fixed_slice_indicator_criterion_Zero
  xi_offslice_fixed_slice_indicator_criterion_zeros :
    Finset xi_offslice_fixed_slice_indicator_criterion_Zero
  xi_offslice_fixed_slice_indicator_criterion_weight :
    xi_offslice_fixed_slice_indicator_criterion_Zero → ℝ
  xi_offslice_fixed_slice_indicator_criterion_weight_pos :
    ∀ z ∈ xi_offslice_fixed_slice_indicator_criterion_zeros,
      0 < xi_offslice_fixed_slice_indicator_criterion_weight z
  xi_offslice_fixed_slice_indicator_criterion_originModulus : ℝ
  xi_offslice_fixed_slice_indicator_criterion_originModulus_eq_exp :
    xi_offslice_fixed_slice_indicator_criterion_originModulus =
      Real.exp
        (-(∑ z ∈ xi_offslice_fixed_slice_indicator_criterion_zeros,
          xi_offslice_fixed_slice_indicator_criterion_weight z))

attribute [instance]
  xi_offslice_fixed_slice_indicator_criterion_data.xi_offslice_fixed_slice_indicator_criterion_fintype
  xi_offslice_fixed_slice_indicator_criterion_data.xi_offslice_fixed_slice_indicator_criterion_decidableEq

namespace xi_offslice_fixed_slice_indicator_criterion_data

/-- The finite off-slice zero set is empty. -/
def zeroSetEmpty (D : xi_offslice_fixed_slice_indicator_criterion_data) : Prop :=
  D.xi_offslice_fixed_slice_indicator_criterion_zeros = ∅

/-- The residual indicator vanishes. -/
def indicatorZero (D : xi_offslice_fixed_slice_indicator_criterion_data) : Prop :=
  D.xi_offslice_fixed_slice_indicator_criterion_zeros.card = 0

/-- The positive weighted zero count vanishes. -/
def weightZero (D : xi_offslice_fixed_slice_indicator_criterion_data) : Prop :=
  (∑ z ∈ D.xi_offslice_fixed_slice_indicator_criterion_zeros,
    D.xi_offslice_fixed_slice_indicator_criterion_weight z) = 0

/-- The Blaschke-origin modulus is one. -/
def originModulusOne (D : xi_offslice_fixed_slice_indicator_criterion_data) : Prop :=
  D.xi_offslice_fixed_slice_indicator_criterion_originModulus = 1

end xi_offslice_fixed_slice_indicator_criterion_data

open xi_offslice_fixed_slice_indicator_criterion_data

/-- Paper label: `prop:xi-offslice-fixed-slice-indicator-criterion`. -/
theorem paper_xi_offslice_fixed_slice_indicator_criterion
    (D : xi_offslice_fixed_slice_indicator_criterion_data) :
    (D.zeroSetEmpty ↔ D.indicatorZero) ∧ (D.indicatorZero ↔ D.weightZero) ∧
      (D.weightZero ↔ D.originModulusOne) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [zeroSetEmpty, indicatorZero, Finset.card_eq_zero]
  · constructor
    · intro hcard
      rw [indicatorZero, Finset.card_eq_zero] at hcard
      simp [weightZero, hcard]
    · intro hsum
      by_contra hcard
      have hnonempty :
          D.xi_offslice_fixed_slice_indicator_criterion_zeros.Nonempty := by
        have hcard_ne :
            D.xi_offslice_fixed_slice_indicator_criterion_zeros.card ≠ 0 := by
          intro hzero
          exact hcard hzero
        exact Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne)
      obtain ⟨z, hz⟩ := hnonempty
      have hpositive :
          0 <
            ∑ x ∈ D.xi_offslice_fixed_slice_indicator_criterion_zeros,
              D.xi_offslice_fixed_slice_indicator_criterion_weight x := by
        exact Finset.sum_pos D.xi_offslice_fixed_slice_indicator_criterion_weight_pos ⟨z, hz⟩
      rw [weightZero] at hsum
      linarith
  · rw [weightZero, originModulusOne,
      D.xi_offslice_fixed_slice_indicator_criterion_originModulus_eq_exp]
    constructor
    · intro hsum
      rw [hsum, neg_zero, Real.exp_zero]
    · intro hexp
      have hneg :
          -(∑ z ∈ D.xi_offslice_fixed_slice_indicator_criterion_zeros,
            D.xi_offslice_fixed_slice_indicator_criterion_weight z) = 0 := by
        have hexp_zero :
            Real.exp
              (-(∑ z ∈ D.xi_offslice_fixed_slice_indicator_criterion_zeros,
                D.xi_offslice_fixed_slice_indicator_criterion_weight z)) = Real.exp 0 := by
          simpa using hexp
        exact Real.exp_eq_exp.mp hexp_zero
      linarith

end Omega.Zeta
