import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite-weight model for functorial Lee--Yang defect transport.  A restricted highest
weight is represented by its coefficients in the fundamental-weight basis; the restricted defect is
the sum of component defects, each bounded by the corresponding coefficient times the fundamental
defect. -/
structure xi_leyang_functoriality_defect_bound_data where
  xi_leyang_functoriality_defect_bound_Index : Type
  xi_leyang_functoriality_defect_bound_fintype :
    Fintype xi_leyang_functoriality_defect_bound_Index
  xi_leyang_functoriality_defect_bound_coeff :
    xi_leyang_functoriality_defect_bound_Index → ℕ
  xi_leyang_functoriality_defect_bound_componentDefect :
    xi_leyang_functoriality_defect_bound_Index → ℝ
  xi_leyang_functoriality_defect_bound_fundamentalDefect :
    xi_leyang_functoriality_defect_bound_Index → ℝ
  xi_leyang_functoriality_defect_bound_restrictedDefect : ℝ
  xi_leyang_functoriality_defect_bound_restrictedDefect_eq :
    xi_leyang_functoriality_defect_bound_restrictedDefect =
      ∑ i,
        xi_leyang_functoriality_defect_bound_componentDefect i
  xi_leyang_functoriality_defect_bound_component_bound :
    ∀ i,
      xi_leyang_functoriality_defect_bound_componentDefect i ≤
        (xi_leyang_functoriality_defect_bound_coeff i : ℝ) *
          xi_leyang_functoriality_defect_bound_fundamentalDefect i

attribute [instance]
  xi_leyang_functoriality_defect_bound_data.xi_leyang_functoriality_defect_bound_fintype

namespace xi_leyang_functoriality_defect_bound_data

/-- Restriction preserves the finite Lee--Yang highest-weight coefficients. -/
def xi_leyang_functoriality_defect_bound_restricted_coeff
    (D : xi_leyang_functoriality_defect_bound_data) :
    D.xi_leyang_functoriality_defect_bound_Index → ℕ :=
  D.xi_leyang_functoriality_defect_bound_coeff

/-- Compactness is represented by vanishing Lee--Yang defect in the finite model. -/
def xi_leyang_functoriality_defect_bound_compact_zero_defect
    (D : xi_leyang_functoriality_defect_bound_data) : Prop :=
  D.xi_leyang_functoriality_defect_bound_restrictedDefect = 0

/-- The coefficientwise upper bound for the restricted highest weight. -/
def xi_leyang_functoriality_defect_bound_upper_bound
    (D : xi_leyang_functoriality_defect_bound_data) : ℝ :=
  ∑ i,
    (D.xi_leyang_functoriality_defect_bound_coeff i : ℝ) *
      D.xi_leyang_functoriality_defect_bound_fundamentalDefect i

end xi_leyang_functoriality_defect_bound_data

open xi_leyang_functoriality_defect_bound_data

/-- Paper-facing conclusion for the finite-weight functoriality defect bound. -/
def xi_leyang_functoriality_defect_bound_conclusion
    (D : xi_leyang_functoriality_defect_bound_data) : Prop :=
  (∀ i,
      D.xi_leyang_functoriality_defect_bound_restricted_coeff i =
        D.xi_leyang_functoriality_defect_bound_coeff i) ∧
    (D.xi_leyang_functoriality_defect_bound_compact_zero_defect ↔
      D.xi_leyang_functoriality_defect_bound_restrictedDefect = 0) ∧
    D.xi_leyang_functoriality_defect_bound_restrictedDefect ≤
      D.xi_leyang_functoriality_defect_bound_upper_bound

lemma xi_leyang_functoriality_defect_bound_upper_bound_proof
    (D : xi_leyang_functoriality_defect_bound_data) :
    D.xi_leyang_functoriality_defect_bound_restrictedDefect ≤
      D.xi_leyang_functoriality_defect_bound_upper_bound := by
  rw [xi_leyang_functoriality_defect_bound_upper_bound,
    D.xi_leyang_functoriality_defect_bound_restrictedDefect_eq]
  exact Finset.sum_le_sum
    (fun i _hi => D.xi_leyang_functoriality_defect_bound_component_bound i)

/-- Paper label: `prop:xi-leyang-functoriality-defect-bound`. -/
theorem paper_xi_leyang_functoriality_defect_bound
    (D : xi_leyang_functoriality_defect_bound_data) :
    xi_leyang_functoriality_defect_bound_conclusion D := by
  refine ⟨?_, ?_, xi_leyang_functoriality_defect_bound_upper_bound_proof D⟩
  · intro i
    rfl
  · rfl

end Omega.Zeta
