import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Omega.Zeta.XiTimePart9pChi2RanktwoResonantFloor

namespace Omega.Zeta

open Filter
open Omega.Folding

noncomputable section

/-- The zero-mode collision excess after subtracting the uniform baseline. -/
def xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_collision_excess
    (m : ℕ) : ℝ :=
  xi_time_part9p_chi2_ranktwo_resonant_floor_collision_mass m - 1

/-- The same normalized collision excess, written as the bin-fold `χ²` term. -/
def xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term
    (m : ℕ) : ℝ :=
  ((foldBinChi2Col m : ℚ) : ℝ)

/-- The two retained Fibonacci resonance modes contribute the positive rank-two floor. -/
def xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant
    (Cphi : ℝ) : ℝ :=
  xi_time_part9p_chi2_ranktwo_resonant_floor_floor Cphi

/-- Bounded three-mode lower envelope: the zero-mode collision excess plus the two Fibonacci
resonances, capped one unit above the resonance floor so its real `liminf` is well-defined by the
order-theoretic API. -/
def xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
    (Cphi : ℝ) (m : ℕ) : ℝ :=
  min
    (xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_collision_excess m +
      xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant Cphi)
    (xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant Cphi + 1)

lemma xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_nonneg
    (m : ℕ) :
    0 ≤ xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term m := by
  have hq : 0 ≤ foldBinChi2Col m := by
    unfold foldBinChi2Col
    exact Finset.sum_nonneg fun x _hx => by
      have hmass : 0 < foldBinUniformMass m := by
        unfold foldBinUniformMass
        positivity
      exact div_nonneg (sq_nonneg (foldBinMass m x - foldBinUniformMass m)) hmass.le
  simpa [xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term] using
    (show (0 : ℝ) ≤ ((foldBinChi2Col m : ℚ) : ℝ) by exact_mod_cast hq)

/-- Paper-facing package: the zero-mode collision excess is the `χ²` term, the retained
Fibonacci pair has positive resonance floor, and the resulting three-mode gap has positive
liminf. -/
def xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_statement : Prop :=
  ∀ Cphi : ℝ,
    (∀ m : ℕ,
      xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_collision_excess m =
        xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term m) ∧
      0 < xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant Cphi ∧
      0 <
        liminf
          (xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
            Cphi)
          atTop

theorem paper_xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable :
    xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_statement := by
  intro Cphi
  have hrank := paper_xi_time_part9p_chi2_ranktwo_resonant_floor
  have hres_pos :
      0 < xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant Cphi :=
    (hrank 0 Cphi).2
  refine ⟨?_, hres_pos, ?_⟩
  · intro m
    have hrewrite := (hrank m Cphi).1
    unfold xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_collision_excess
      xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term
    linarith
  · have hfloor_le :
        xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant Cphi ≤
          liminf
            (xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
              Cphi)
            atTop := by
      have hbounded :
          IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop
            (xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
              Cphi) := by
        refine IsCoboundedUnder.of_frequently_le
          (a := xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant
            Cphi + 1) (Frequently.of_forall ?_)
        intro m
        unfold
          xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
        exact min_le_right _ _
      refine le_liminf_of_le hbounded (Eventually.of_forall ?_)
      intro m
      have hchi2_nonneg :=
        xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_nonneg m
      have hchi2_nonneg' : 0 ≤ ((foldBinChi2Col m : ℚ) : ℝ) := by
        simpa [xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_chi2_term] using
          hchi2_nonneg
      have hrewrite := (hrank m Cphi).1
      unfold
        xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_three_mode_gap_lower_envelope
      refine le_min ?_ ?_
      · unfold xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_collision_excess
          xi_time_part63b_three_mode_gap_zero_mode_nonrenormalizable_resonance_constant
        linarith
      · linarith
    exact lt_of_lt_of_le hres_pos hfloor_le

end

end Omega.Zeta
