import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-fiber data for the capacity/overlap/L¹ identity. -/
structure xi_capacity_overlap_functional_l1_identity_data where
  xi_capacity_overlap_functional_l1_identity_fiberSize : ℕ
  xi_capacity_overlap_functional_l1_identity_normalizedCapacity : ℝ
  xi_capacity_overlap_functional_l1_identity_pushforwardMass :
    Fin xi_capacity_overlap_functional_l1_identity_fiberSize → ℝ
  xi_capacity_overlap_functional_l1_identity_uniformLayerMass :
    Fin xi_capacity_overlap_functional_l1_identity_fiberSize → ℝ
  xi_capacity_overlap_functional_l1_identity_tau : ℝ
  xi_capacity_overlap_functional_l1_identity_l1Distance : ℝ
  xi_capacity_overlap_functional_l1_identity_binBudgetSuccess : ℝ
  xi_capacity_overlap_functional_l1_identity_normalizedCapacity_eq :
    xi_capacity_overlap_functional_l1_identity_normalizedCapacity =
      ∑ x,
        min (xi_capacity_overlap_functional_l1_identity_pushforwardMass x)
          (xi_capacity_overlap_functional_l1_identity_tau *
            xi_capacity_overlap_functional_l1_identity_uniformLayerMass x)
  xi_capacity_overlap_functional_l1_identity_pushforwardMass_sum :
    ∑ x, xi_capacity_overlap_functional_l1_identity_pushforwardMass x = 1
  xi_capacity_overlap_functional_l1_identity_uniformLayerMass_sum :
    ∑ x, xi_capacity_overlap_functional_l1_identity_uniformLayerMass x = 1
  xi_capacity_overlap_functional_l1_identity_l1Distance_eq :
    xi_capacity_overlap_functional_l1_identity_l1Distance =
      ∑ x,
        |xi_capacity_overlap_functional_l1_identity_pushforwardMass x -
          xi_capacity_overlap_functional_l1_identity_tau *
            xi_capacity_overlap_functional_l1_identity_uniformLayerMass x|
  xi_capacity_overlap_functional_l1_identity_binBudgetSuccess_eq :
    xi_capacity_overlap_functional_l1_identity_binBudgetSuccess =
      xi_capacity_overlap_functional_l1_identity_normalizedCapacity

namespace xi_capacity_overlap_functional_l1_identity_data

/-- Truncated overlap of the pushforward mass with the scaled uniform layer mass. -/
def truncatedOverlap (D : xi_capacity_overlap_functional_l1_identity_data) : ℝ :=
  ∑ x,
    min (D.xi_capacity_overlap_functional_l1_identity_pushforwardMass x)
      (D.xi_capacity_overlap_functional_l1_identity_tau *
        D.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x)

/-- The right-hand side of the finite-fiber L¹ identity. -/
def l1Formula (D : xi_capacity_overlap_functional_l1_identity_data) : ℝ :=
  (1 + D.xi_capacity_overlap_functional_l1_identity_tau -
    D.xi_capacity_overlap_functional_l1_identity_l1Distance) / 2

/-- Normalized capacity equals the truncated overlap sum. -/
def normalizedCapacity_eq_truncatedOverlap
    (D : xi_capacity_overlap_functional_l1_identity_data) : Prop :=
  D.xi_capacity_overlap_functional_l1_identity_normalizedCapacity = D.truncatedOverlap

/-- The truncated overlap sum is the standard `L¹` formula. -/
def truncatedOverlap_eq_l1Formula
    (D : xi_capacity_overlap_functional_l1_identity_data) : Prop :=
  D.truncatedOverlap = D.l1Formula

/-- The bin-budget success probability is the same `L¹` formula. -/
def binBudgetSuccess_eq_l1Formula
    (D : xi_capacity_overlap_functional_l1_identity_data) : Prop :=
  D.xi_capacity_overlap_functional_l1_identity_binBudgetSuccess = D.l1Formula

end xi_capacity_overlap_functional_l1_identity_data

lemma xi_capacity_overlap_functional_l1_identity_min_eq_l1_half (a b : ℝ) :
    min a b = (a + b - |a - b|) / 2 := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Paper label: `thm:xi-capacity-overlap-functional-l1-identity`. -/
theorem paper_xi_capacity_overlap_functional_l1_identity
    (h : xi_capacity_overlap_functional_l1_identity_data) :
    h.normalizedCapacity_eq_truncatedOverlap ∧ h.truncatedOverlap_eq_l1Formula ∧
      h.binBudgetSuccess_eq_l1Formula := by
  have hnormalized : h.normalizedCapacity_eq_truncatedOverlap := by
    rw [xi_capacity_overlap_functional_l1_identity_data.normalizedCapacity_eq_truncatedOverlap,
      xi_capacity_overlap_functional_l1_identity_data.truncatedOverlap]
    exact h.xi_capacity_overlap_functional_l1_identity_normalizedCapacity_eq
  have hoverlap : h.truncatedOverlap_eq_l1Formula := by
    rw [xi_capacity_overlap_functional_l1_identity_data.truncatedOverlap_eq_l1Formula,
      xi_capacity_overlap_functional_l1_identity_data.truncatedOverlap,
      xi_capacity_overlap_functional_l1_identity_data.l1Formula]
    calc
      (∑ x,
          min (h.xi_capacity_overlap_functional_l1_identity_pushforwardMass x)
            (h.xi_capacity_overlap_functional_l1_identity_tau *
              h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x)) =
          ∑ x,
            (h.xi_capacity_overlap_functional_l1_identity_pushforwardMass x +
                h.xi_capacity_overlap_functional_l1_identity_tau *
                  h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x -
              |h.xi_capacity_overlap_functional_l1_identity_pushforwardMass x -
                h.xi_capacity_overlap_functional_l1_identity_tau *
                  h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x|) / 2 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact xi_capacity_overlap_functional_l1_identity_min_eq_l1_half _ _
      _ =
          (∑ x,
              (h.xi_capacity_overlap_functional_l1_identity_pushforwardMass x +
                  h.xi_capacity_overlap_functional_l1_identity_tau *
                    h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x -
                |h.xi_capacity_overlap_functional_l1_identity_pushforwardMass x -
                  h.xi_capacity_overlap_functional_l1_identity_tau *
                    h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass x|)) / 2 := by
            rw [Finset.sum_div]
      _ =
          (1 + h.xi_capacity_overlap_functional_l1_identity_tau -
              h.xi_capacity_overlap_functional_l1_identity_l1Distance) / 2 := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum,
              h.xi_capacity_overlap_functional_l1_identity_pushforwardMass_sum,
              h.xi_capacity_overlap_functional_l1_identity_uniformLayerMass_sum,
              ← h.xi_capacity_overlap_functional_l1_identity_l1Distance_eq]
            ring
  refine ⟨hnormalized, hoverlap, ?_⟩
  rw [xi_capacity_overlap_functional_l1_identity_data.binBudgetSuccess_eq_l1Formula]
  calc
    h.xi_capacity_overlap_functional_l1_identity_binBudgetSuccess =
        h.xi_capacity_overlap_functional_l1_identity_normalizedCapacity := by
        exact h.xi_capacity_overlap_functional_l1_identity_binBudgetSuccess_eq
    _ = h.truncatedOverlap := hnormalized
    _ = h.l1Formula := hoverlap

end

end Omega.Zeta
