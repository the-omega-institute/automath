import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalFixedOrderFreezingThreshold

namespace Omega.Zeta

open Filter
open scoped Topology

noncomputable section

/-- Concrete asymptotic data for terminal fixed-order escort concentration on the max-fiber set. -/
structure xi_terminal_fixed_order_escort_maxfiber_concentration_data where
  xi_terminal_fixed_order_escort_maxfiber_concentration_a : ℕ
  xi_terminal_fixed_order_escort_maxfiber_concentration_X : ℕ → ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_K : ℕ → ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_M : ℕ → ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_M2 : ℕ → ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass : ℕ → ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_gamma : ℝ
  xi_terminal_fixed_order_escort_maxfiber_concentration_a_ge_critical :
    xiTerminalFixedOrderCritical ≤ xi_terminal_fixed_order_escort_maxfiber_concentration_a
  xi_terminal_fixed_order_escort_maxfiber_concentration_gamma_pos :
    0 < xi_terminal_fixed_order_escort_maxfiber_concentration_gamma
  xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass_nonneg :
    ∀ m : ℕ, 0 ≤ xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass m
  xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass_bound :
    ∀ m : ℕ,
      xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass m ≤
        xi_terminal_fixed_order_escort_maxfiber_concentration_X m *
            xi_terminal_fixed_order_escort_maxfiber_concentration_M2 m ^
              xi_terminal_fixed_order_escort_maxfiber_concentration_a /
          (xi_terminal_fixed_order_escort_maxfiber_concentration_K m *
            xi_terminal_fixed_order_escort_maxfiber_concentration_M m ^
              xi_terminal_fixed_order_escort_maxfiber_concentration_a)
  xi_terminal_fixed_order_escort_maxfiber_concentration_majorant_eq :
    ∀ m : ℕ,
      xi_terminal_fixed_order_escort_maxfiber_concentration_X m *
            xi_terminal_fixed_order_escort_maxfiber_concentration_M2 m ^
              xi_terminal_fixed_order_escort_maxfiber_concentration_a /
          (xi_terminal_fixed_order_escort_maxfiber_concentration_K m *
            xi_terminal_fixed_order_escort_maxfiber_concentration_M m ^
              xi_terminal_fixed_order_escort_maxfiber_concentration_a) =
        Real.exp
          (-xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ))

/-- The explicit complement/lead majorant from the max-fiber estimate. -/
def xi_terminal_fixed_order_escort_maxfiber_concentration_majorant
    (D : xi_terminal_fixed_order_escort_maxfiber_concentration_data) (m : ℕ) : ℝ :=
  D.xi_terminal_fixed_order_escort_maxfiber_concentration_X m *
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_M2 m ^
        D.xi_terminal_fixed_order_escort_maxfiber_concentration_a /
    (D.xi_terminal_fixed_order_escort_maxfiber_concentration_K m *
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_M m ^
        D.xi_terminal_fixed_order_escort_maxfiber_concentration_a)

/-- Paper-facing concentration claim: the fixed order is frozen, the complement escort mass
vanishes, and the logarithmic majorant has exponent `-gamma`. -/
def xi_terminal_fixed_order_escort_maxfiber_concentration_claim
    (D : xi_terminal_fixed_order_escort_maxfiber_concentration_data) : Prop :=
  (∀ m : ℕ,
    xiTerminalOffMaxContribution
        D.xi_terminal_fixed_order_escort_maxfiber_concentration_a m ≤
      xiTerminalMaxContribution
        D.xi_terminal_fixed_order_escort_maxfiber_concentration_a m) ∧
    Tendsto D.xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass atTop (𝓝 0) ∧
      Tendsto
        (fun m : ℕ =>
          Real.log (xi_terminal_fixed_order_escort_maxfiber_concentration_majorant D m) /
            (m : ℝ))
        atTop (𝓝 (-D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma))

/-- Paper label: `cor:xi-terminal-fixed-order-escort-maxfiber-concentration`. -/
theorem paper_xi_terminal_fixed_order_escort_maxfiber_concentration
    (D : xi_terminal_fixed_order_escort_maxfiber_concentration_data) :
    xi_terminal_fixed_order_escort_maxfiber_concentration_claim D := by
  have hthreshold :
      ∀ m : ℕ,
        xiTerminalOffMaxContribution
            D.xi_terminal_fixed_order_escort_maxfiber_concentration_a m ≤
          xiTerminalMaxContribution
            D.xi_terminal_fixed_order_escort_maxfiber_concentration_a m := by
    intro m
    exact (paper_xi_terminal_fixed_order_freezing_threshold.2.1
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_a m
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_a_ge_critical)
  have hmajorant_exp :
      ∀ m : ℕ,
        xi_terminal_fixed_order_escort_maxfiber_concentration_majorant D m =
          Real.exp
            (-D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ)) := by
    intro m
    simpa [xi_terminal_fixed_order_escort_maxfiber_concentration_majorant] using
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_majorant_eq m
  have hmajorant_tendsto_zero :
      Tendsto (xi_terminal_fixed_order_escort_maxfiber_concentration_majorant D) atTop (𝓝 0) := by
    have hlin :
        Tendsto
          (fun m : ℕ =>
            -D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ))
          atTop atBot := by
      have hpos :
          Tendsto
            (fun m : ℕ =>
              D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ))
            atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
          D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma_pos
      have hneg :
          Tendsto
            (fun m : ℕ =>
              -(D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ)))
            atTop atBot := by
        simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp hpos
      simpa [neg_mul] using hneg
    have hexp :
        Tendsto
          (fun m : ℕ =>
            Real.exp
              (-D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma * (m : ℝ)))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hlin
    exact hexp.congr' (Eventually.of_forall fun m => (hmajorant_exp m).symm)
  have houtside_tendsto_zero :
      Tendsto D.xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass atTop (𝓝 0) := by
    refine squeeze_zero
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass_nonneg ?_
      hmajorant_tendsto_zero
    intro m
    simpa [xi_terminal_fixed_order_escort_maxfiber_concentration_majorant] using
      D.xi_terminal_fixed_order_escort_maxfiber_concentration_outsideMass_bound m
  have hlog_tendsto :
      Tendsto
        (fun m : ℕ =>
          Real.log (xi_terminal_fixed_order_escort_maxfiber_concentration_majorant D m) /
            (m : ℝ))
        atTop (𝓝 (-D.xi_terminal_fixed_order_escort_maxfiber_concentration_gamma)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    rw [hmajorant_exp m, Real.log_exp]
    field_simp [hm_ne]
  exact ⟨hthreshold, houtside_tendsto_zero, hlog_tendsto⟩

end

end Omega.Zeta
