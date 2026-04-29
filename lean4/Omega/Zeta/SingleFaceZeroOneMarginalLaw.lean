import Mathlib.Tactic

namespace Omega.Zeta

/-- Component count after adding one edge to a graph whose endpoints are already in the same
component exactly when `sameComponent` is true. -/
def xi_time_part65f_single_face_zero_one_marginal_law_component_count_after
    (componentCount : ℕ) (sameComponent : Bool) : ℕ :=
  if sameComponent then componentCount else componentCount - 1

/-- Screen-kernel dimension from the component formula `δ = c - 1`. -/
def xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect
    (componentCount : ℕ) : ℕ :=
  componentCount - 1

/-- Rank recovered from a fixed ambient dimension and the screen-kernel defect. -/
def xi_time_part65f_single_face_zero_one_marginal_law_rank
    (ambientRank componentCount : ℕ) : ℕ :=
  ambientRank -
    xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect componentCount

/-- Paper label: `thm:xi-time-part65f-single-face-zero-one-marginal-law`.
Adding one edge either preserves the component count or merges exactly two components, hence
the kernel-defect drop and rank increment are both the corresponding `0`--`1` value. -/
theorem paper_xi_time_part65f_single_face_zero_one_marginal_law
    (ambientRank componentCount : ℕ) (sameComponent : Bool)
    (_hcomponent_pos : 0 < componentCount)
    (hdifferent_two : sameComponent = false → 1 < componentCount)
    (hdefect_le :
      xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect componentCount ≤
        ambientRank) :
    let componentCountAfter :=
      xi_time_part65f_single_face_zero_one_marginal_law_component_count_after
        componentCount sameComponent
    let gain := if sameComponent then 0 else 1
    xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect componentCount -
        xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect componentCountAfter =
          gain ∧
      xi_time_part65f_single_face_zero_one_marginal_law_rank ambientRank componentCountAfter -
          xi_time_part65f_single_face_zero_one_marginal_law_rank ambientRank componentCount =
            gain := by
  dsimp
  by_cases hsame : sameComponent = true
  · subst sameComponent
    simp [xi_time_part65f_single_face_zero_one_marginal_law_component_count_after]
  · have hfalse : sameComponent = false := by
      cases sameComponent <;> simp_all
    have htwo : 1 < componentCount := hdifferent_two hfalse
    have hdefect_le' : componentCount - 1 ≤ ambientRank := by
      simpa [xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect] using hdefect_le
    subst sameComponent
    simp [xi_time_part65f_single_face_zero_one_marginal_law_component_count_after,
      xi_time_part65f_single_face_zero_one_marginal_law_kernel_defect,
      xi_time_part65f_single_face_zero_one_marginal_law_rank]
    omega

end Omega.Zeta
