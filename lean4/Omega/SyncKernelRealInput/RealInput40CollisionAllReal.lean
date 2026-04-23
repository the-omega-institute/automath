import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Omega.Zeta.ArityCollisionQuadraticClosed

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:real-input-40-collision-all-real`. The pure-collision cubic from the Zeta
package has negative, central, and Perron roots separated by explicit sign changes, and its cubic
discriminant is the displayed positive polynomial in `u`. -/
theorem paper_real_input_40_collision_all_real (u : ℝ) (hu : 0 < u) :
    0 < 4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8 ∧
      ∃ lm l0 lp : ℝ,
        lm < 0 ∧
          0 < l0 ∧
          l0 < 1 ∧
          1 < lp ∧
          lm ^ 3 - 2 * lm ^ 2 - (u + 1) * lm + u = 0 ∧
          l0 ^ 3 - 2 * l0 ^ 2 - (u + 1) * l0 + u = 0 ∧
          lp ^ 3 - 2 * lp ^ 2 - (u + 1) * lp + u = 0 := by
  have hdisc : 0 < 4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8 := by
    positivity
  have hcubic_cont : Continuous (Omega.Zeta.arityCollisionPureCubic u) := by
    unfold Omega.Zeta.arityCollisionPureCubic
    continuity
  have hneg_cubic_cont : Continuous fun x : ℝ => -Omega.Zeta.arityCollisionPureCubic u x := by
    continuity
  have hleft_neg : Omega.Zeta.arityCollisionPureCubic u (-(u + 1)) < 0 := by
    unfold Omega.Zeta.arityCollisionPureCubic
    nlinarith [hu]
  have hzero_pos : 0 < Omega.Zeta.arityCollisionPureCubic u 0 := by
    simpa [Omega.Zeta.arityCollisionPureCubic] using hu
  have hone_neg : Omega.Zeta.arityCollisionPureCubic u 1 < 0 := by
    unfold Omega.Zeta.arityCollisionPureCubic
    nlinarith
  have htwo_neg : Omega.Zeta.arityCollisionPureCubic u 2 < 0 := by
    unfold Omega.Zeta.arityCollisionPureCubic
    nlinarith
  have hright_pos : 0 < Omega.Zeta.arityCollisionPureCubic u (u + 3) := by
    unfold Omega.Zeta.arityCollisionPureCubic
    nlinarith [hu]
  have hzero_left_mem :
      (0 : ℝ) ∈ Set.Ioo (Omega.Zeta.arityCollisionPureCubic u (-(u + 1)))
        (Omega.Zeta.arityCollisionPureCubic u 0) := by
    exact ⟨hleft_neg, hzero_pos⟩
  rcases intermediate_value_Ioo (show -(u + 1 : ℝ) ≤ 0 by linarith) hcubic_cont.continuousOn
    hzero_left_mem with ⟨lm, hlm_mem, hlm_root⟩
  have hzero_mid_mem :
      (0 : ℝ) ∈ Set.Ioo (-(Omega.Zeta.arityCollisionPureCubic u 0))
        (-(Omega.Zeta.arityCollisionPureCubic u 1)) := by
    constructor <;> linarith
  rcases intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num) hneg_cubic_cont.continuousOn
    hzero_mid_mem with ⟨l0, hl0_mem, hl0_root_neg⟩
  have hl0_root : Omega.Zeta.arityCollisionPureCubic u l0 = 0 := by
    linarith
  have hzero_right_mem :
      (0 : ℝ) ∈ Set.Ioo (Omega.Zeta.arityCollisionPureCubic u 2)
        (Omega.Zeta.arityCollisionPureCubic u (u + 3)) := by
    exact ⟨htwo_neg, hright_pos⟩
  rcases intermediate_value_Ioo (show (2 : ℝ) ≤ u + 3 by linarith) hcubic_cont.continuousOn
    hzero_right_mem with ⟨lp, hlp_mem, hlp_root⟩
  refine ⟨hdisc, lm, l0, lp, hlm_mem.2, hl0_mem.1, hl0_mem.2, ?_, ?_, ?_, ?_⟩
  · linarith [hlp_mem.1]
  · simpa [Omega.Zeta.arityCollisionPureCubic] using hlm_root
  · simpa [Omega.Zeta.arityCollisionPureCubic] using hl0_root
  · simpa [Omega.Zeta.arityCollisionPureCubic] using hlp_root

end Omega.SyncKernelRealInput
