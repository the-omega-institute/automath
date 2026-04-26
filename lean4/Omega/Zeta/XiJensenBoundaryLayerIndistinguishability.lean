import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The boundary-layer zero radius `|a| = exp (-η)`. -/
def xi_jensen_boundary_layer_indistinguishability_boundaryRadius (η : ℝ) : ℝ :=
  Real.exp (-η)

/-- The zero-free comparison function. -/
def xi_jensen_boundary_layer_indistinguishability_F0 : ℂ → ℂ :=
  fun _ => 1

/-- The single-zero boundary-layer perturbation. -/
def xi_jensen_boundary_layer_indistinguishability_F1 (a : ℂ) : ℂ → ℂ :=
  fun w => 1 - w / a

/-- Jensen defect for a single zero at radius `a`. -/
def xi_jensen_boundary_layer_indistinguishability_jensenDefect (a r : ℝ) : ℝ :=
  if r ≤ a then 0 else Real.log (r / a)

/-- Concrete witness package for the indistinguishable boundary-layer pair. -/
def xi_jensen_boundary_layer_indistinguishability_existsIndistinguishableBoundaryLayerPair
    (ε η : ℝ) : Prop :=
  ∃ a : ℂ,
    ‖a‖ = xi_jensen_boundary_layer_indistinguishability_boundaryRadius η ∧
    a ≠ 0 ∧
    xi_jensen_boundary_layer_indistinguishability_F0 0 = 1 ∧
    xi_jensen_boundary_layer_indistinguishability_F1 a 0 = 1 ∧
    xi_jensen_boundary_layer_indistinguishability_F1 a a = 0 ∧
    (∀ r, 0 < r → r < 1 →
      |xi_jensen_boundary_layer_indistinguishability_jensenDefect
          (xi_jensen_boundary_layer_indistinguishability_boundaryRadius η) r| ≤ ε) ∧
    |xi_jensen_boundary_layer_indistinguishability_jensenDefect
        (xi_jensen_boundary_layer_indistinguishability_boundaryRadius η)
        (Real.exp (-η / 2))| = η / 2

private lemma xi_jensen_boundary_layer_indistinguishability_boundaryRadius_pos (η : ℝ) :
    0 < xi_jensen_boundary_layer_indistinguishability_boundaryRadius η := by
  exact Real.exp_pos (-η)

/-- Paper label: `thm:xi-jensen-boundary-layer-indistinguishability`. The explicit witnesses
`F₀(w) = 1` and `F₁(w) = 1 - w / a` with `|a| = exp (-η)` have Jensen defects that differ by at
most `η` on the whole radius interval and approach that bound arbitrarily closely. -/
theorem paper_xi_jensen_boundary_layer_indistinguishability
    (ε η : ℝ) (hη : 0 < η) (hηε : η ≤ ε) :
    xi_jensen_boundary_layer_indistinguishability_existsIndistinguishableBoundaryLayerPair ε η := by
  refine ⟨(xi_jensen_boundary_layer_indistinguishability_boundaryRadius η : ℂ), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simpa [xi_jensen_boundary_layer_indistinguishability_boundaryRadius, abs_of_pos (Real.exp_pos _)]
      using Complex.norm_real (Real.exp (-η))
  · exact_mod_cast (xi_jensen_boundary_layer_indistinguishability_boundaryRadius_pos η).ne'
  · rfl
  · simp [xi_jensen_boundary_layer_indistinguishability_F1]
  ·
    have ha :
        (xi_jensen_boundary_layer_indistinguishability_boundaryRadius η : ℂ) ≠ 0 := by
      exact_mod_cast (xi_jensen_boundary_layer_indistinguishability_boundaryRadius_pos η).ne'
    simp [xi_jensen_boundary_layer_indistinguishability_F1, ha]
  · intro r hr0 hr1
    by_cases hrle :
        r ≤ xi_jensen_boundary_layer_indistinguishability_boundaryRadius η
    · have hεnonneg : 0 ≤ ε := le_trans (le_of_lt hη) hηε
      simp [xi_jensen_boundary_layer_indistinguishability_jensenDefect, hrle, hεnonneg]
    · have hra :
          xi_jensen_boundary_layer_indistinguishability_boundaryRadius η < r :=
        lt_of_not_ge hrle
      have ha_pos :
          0 < xi_jensen_boundary_layer_indistinguishability_boundaryRadius η :=
        xi_jensen_boundary_layer_indistinguishability_boundaryRadius_pos η
      have hratio_pos : 0 < r / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η :=
        div_pos hr0 ha_pos
      have hratio_ge_one : 1 ≤ r / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η := by
        rw [one_le_div ha_pos]
        exact hra.le
      have hlog_nonneg : 0 ≤
          Real.log (r / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η) :=
        Real.log_nonneg hratio_ge_one
      have hratio_lt :
          r / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η < Real.exp η := by
        rw [xi_jensen_boundary_layer_indistinguishability_boundaryRadius]
        refine (div_lt_iff₀ (Real.exp_pos (-η))).2 ?_
        calc
          r < 1 := hr1
          _ = Real.exp η * Real.exp (-η) := by
            rw [← Real.exp_add]
            ring_nf
            simp
      have hlog_lt :
          Real.log (r / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η) < η := by
        rw [xi_jensen_boundary_layer_indistinguishability_boundaryRadius]
        have := Real.log_lt_log hratio_pos hratio_lt
        simpa using this
      rw [xi_jensen_boundary_layer_indistinguishability_jensenDefect, if_neg hrle,
        abs_of_nonneg hlog_nonneg]
      exact le_trans (le_of_lt hlog_lt) hηε
  · have hmid_gt :
        xi_jensen_boundary_layer_indistinguishability_boundaryRadius η < Real.exp (-η / 2) := by
      rw [xi_jensen_boundary_layer_indistinguishability_boundaryRadius]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hmid_not_le :
        ¬Real.exp (-η / 2) ≤ xi_jensen_boundary_layer_indistinguishability_boundaryRadius η :=
      not_le_of_gt hmid_gt
    have hmid_nonneg :
        0 ≤ Real.log
          (Real.exp (-η / 2) / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η) := by
      have hratio_ge_one :
          1 ≤ Real.exp (-η / 2) / xi_jensen_boundary_layer_indistinguishability_boundaryRadius η := by
        rw [one_le_div (xi_jensen_boundary_layer_indistinguishability_boundaryRadius_pos η)]
        exact hmid_gt.le
      exact Real.log_nonneg hratio_ge_one
    rw [xi_jensen_boundary_layer_indistinguishability_jensenDefect, if_neg hmid_not_le,
      abs_of_nonneg hmid_nonneg, xi_jensen_boundary_layer_indistinguishability_boundaryRadius]
    have hexp_eq : Real.exp (-η / 2) / Real.exp (-η) = Real.exp (η / 2) := by
      rw [← Real.exp_sub]
      ring_nf
    rw [hexp_eq, Real.log_exp]

end

end Omega.Zeta
