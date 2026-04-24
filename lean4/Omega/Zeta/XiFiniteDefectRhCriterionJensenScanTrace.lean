import Mathlib.Tactic
import Omega.Zeta.XiJensenBoundaryPotentialFiniteDefectExplicit

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The zero-frequency Jensen scan trace in the finite-defect model. -/
def xi_finite_defect_rh_criterion_jensen_scan_trace_zeroMode
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ) : ℝ :=
  (1 / (4 * Real.pi)) *
    ∫ x, xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x

/-- Paper label: `thm:xi-finite-defect-rh-criterion-jensen-scan-trace`. The concrete Lean
surrogate identifies the zero-mode Jensen scan trace with the weighted total defect depth and
therefore characterizes its vanishing by the absence of defect multiplicities. -/
theorem paper_xi_finite_defect_rh_criterion_jensen_scan_trace
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ)
    (hδ : ∀ i, 0 < δ i) :
    xi_finite_defect_rh_criterion_jensen_scan_trace_zeroMode γ δ m =
        ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) ∧
      (xi_finite_defect_rh_criterion_jensen_scan_trace_zeroMode γ δ m = 0 ↔
        ∀ i, m i = 0) := by
  have hprofile := paper_xi_jensen_boundary_potential_finite_defect_explicit γ δ m hδ
  have htrace :
      xi_finite_defect_rh_criterion_jensen_scan_trace_zeroMode γ δ m =
        ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by
    have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
    unfold xi_finite_defect_rh_criterion_jensen_scan_trace_zeroMode
    calc
      (1 / (4 * Real.pi)) *
          ∫ x, xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x =
        (1 / (4 * Real.pi)) * (4 * Real.pi * ∑ i, (m i : ℝ) * (δ i / (1 + δ i))) := by
          rw [hprofile.2.2.1]
      _ = ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by
          field_simp [h4pi_ne]
  refine ⟨htrace, ?_⟩
  constructor
  · intro hzero i
    by_cases hmi : m i = 0
    · exact hmi
    · exfalso
      have hden_i : 0 < 1 + δ i := add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (hδ i))
      have hfactor_pos : 0 < δ i / (1 + δ i) := by
        exact div_pos (hδ i) hden_i
      have hm_pos : 0 < (m i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hmi
      have hterm_pos : 0 < (m i : ℝ) * (δ i / (1 + δ i)) := mul_pos hm_pos hfactor_pos
      have hterm_nonneg :
          ∀ j : ι, 0 ≤ (m j : ℝ) * (δ j / (1 + δ j)) := by
        intro j
        have hden_j : 0 < 1 + δ j := add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (hδ j))
        have hfactor_nonneg : 0 ≤ δ j / (1 + δ j) := le_of_lt <| div_pos (hδ j) hden_j
        exact mul_nonneg (by exact_mod_cast Nat.zero_le (m j)) hfactor_nonneg
      have hsum_zero : ∑ j, (m j : ℝ) * (δ j / (1 + δ j)) = 0 := by
        simpa [htrace] using hzero
      have hle :
          (m i : ℝ) * (δ i / (1 + δ i)) ≤ ∑ j, (m j : ℝ) * (δ j / (1 + δ j)) := by
        exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
      have hle_zero : (m i : ℝ) * (δ i / (1 + δ i)) ≤ 0 := by
        simpa [hsum_zero] using hle
      exact not_le_of_gt hterm_pos hle_zero
  · intro hmzero
    rw [htrace]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hmzero i]

end

end Omega.Zeta
