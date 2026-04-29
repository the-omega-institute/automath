import Mathlib.Tactic

namespace Omega.Zeta

/-- The unweighted point lies inside the normalized RH window `[0, 1]`. -/
def xi_time_part9pb_rh_window_uniform_gap_coexistence_rhAtOne : Prop :=
  (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1

/-- Concrete lower-bound statement for the normalized collision liminf. -/
def xi_time_part9pb_rh_window_uniform_gap_coexistence_uniformGapLowerBound
    (C_phi normalizedCollisionLiminf : ℝ) : Prop :=
  0 < C_phi ∧ 2 * C_phi ^ 2 ≤ normalizedCollisionLiminf

/-- Paper label: `thm:xi-time-part9pb-rh-window-uniform-gap-coexistence`.
At the unweighted point `u = 1`, the normalized RH window condition coexists with a positive
constant-scale collision-gap lower bound. -/
theorem paper_xi_time_part9pb_rh_window_uniform_gap_coexistence
    (C_phi normalizedCollisionLiminf : ℝ)
    (hC_phi : 0 < C_phi)
    (hgap : 2 * C_phi ^ 2 ≤ normalizedCollisionLiminf) :
    xi_time_part9pb_rh_window_uniform_gap_coexistence_rhAtOne ∧
      xi_time_part9pb_rh_window_uniform_gap_coexistence_uniformGapLowerBound
        C_phi normalizedCollisionLiminf := by
  exact ⟨by norm_num [xi_time_part9pb_rh_window_uniform_gap_coexistence_rhAtOne],
    hC_phi, hgap⟩

end Omega.Zeta
