import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

open Filter
open scoped BigOperators

/-- The shared finite Stokes contribution after truncating the one-dimensional germ expansion. -/
def xi_time_part70e_stokes_normalization_rigidity_finite_stokes_sum
    (coefficient : ℕ → ℝ) (mode : ℕ → ℕ → ℝ) (R m : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 R) fun r => coefficient r * mode r m

/-- The target-normalized constant left after the common finite Stokes term cancels. -/
def xi_time_part70e_stokes_normalization_rigidity_constant (c : ℝ) : ℝ :=
  Real.exp (c - Real.log (2 * Real.pi))

/-- Concrete logarithmic expansion template for the `G_m` side. -/
def xi_time_part70e_stokes_normalization_rigidity_G_expansion
    (G sharedTerm remainderG : ℕ → ℝ) (c : ℝ) (m : ℕ) : Prop :=
  Real.log (G m) = c + sharedTerm m + remainderG m

/-- Concrete logarithmic expansion template for the `C_m` normalization side. -/
def xi_time_part70e_stokes_normalization_rigidity_C_expansion
    (C sharedTerm remainderC : ℕ → ℝ) (m : ℕ) : Prop :=
  Real.log (C m) = Real.log (2 * Real.pi) + sharedTerm m + remainderC m

lemma xi_time_part70e_stokes_normalization_rigidity_log_difference
    (G C sharedTerm remainderG remainderC : ℕ → ℝ) (c : ℝ) (m : ℕ)
    (hG :
      xi_time_part70e_stokes_normalization_rigidity_G_expansion
        G sharedTerm remainderG c m)
    (hC :
      xi_time_part70e_stokes_normalization_rigidity_C_expansion
        C sharedTerm remainderC m) :
    Real.log (G m) - Real.log (C m) =
      c - Real.log (2 * Real.pi) + (remainderG m - remainderC m) := by
  unfold xi_time_part70e_stokes_normalization_rigidity_G_expansion at hG
  unfold xi_time_part70e_stokes_normalization_rigidity_C_expansion at hC
  rw [hG, hC]
  ring

/-- Paper label: `thm:xi-time-part70e-stokes-normalization-rigidity`.

If the two logarithmic Stokes expansions have the same truncated finite term and both remainders
vanish, subtracting the two expansions leaves only the normalization constant; continuity of
`exp` then gives the ratio limit. -/
theorem paper_xi_time_part70e_stokes_normalization_rigidity
    (G C sharedTerm remainderG remainderC : ℕ → ℝ) (c : ℝ)
    (hG_pos : ∀ᶠ m in atTop, 0 < G m)
    (hC_pos : ∀ᶠ m in atTop, 0 < C m)
    (hG :
      ∀ᶠ m in atTop,
        xi_time_part70e_stokes_normalization_rigidity_G_expansion
          G sharedTerm remainderG c m)
    (hC :
      ∀ᶠ m in atTop,
        xi_time_part70e_stokes_normalization_rigidity_C_expansion
          C sharedTerm remainderC m)
    (hremainderG : Tendsto remainderG atTop (nhds 0))
    (hremainderC : Tendsto remainderC atTop (nhds 0)) :
    Tendsto (fun m => G m / C m) atTop
      (nhds (xi_time_part70e_stokes_normalization_rigidity_constant c)) := by
  have hremainder :
      Tendsto (fun m => remainderG m - remainderC m) atTop (nhds 0) := by
    simpa using hremainderG.sub hremainderC
  have hlog :
      Tendsto (fun m => Real.log (G m) - Real.log (C m)) atTop
        (nhds (c - Real.log (2 * Real.pi))) := by
    have hsum :
        Tendsto (fun m => c - Real.log (2 * Real.pi) + (remainderG m - remainderC m))
          atTop (nhds (c - Real.log (2 * Real.pi) + 0)) := by
      exact tendsto_const_nhds.add hremainder
    have hsum' :
        Tendsto (fun m => c - Real.log (2 * Real.pi) + (remainderG m - remainderC m))
          atTop (nhds (c - Real.log (2 * Real.pi))) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards [hG, hC] with m hmG hmC
    exact (xi_time_part70e_stokes_normalization_rigidity_log_difference
      G C sharedTerm remainderG remainderC c m hmG hmC).symm
  have hexp :
      Tendsto (fun m => Real.exp (Real.log (G m) - Real.log (C m))) atTop
        (nhds (xi_time_part70e_stokes_normalization_rigidity_constant c)) := by
    simpa [xi_time_part70e_stokes_normalization_rigidity_constant] using
      Real.continuous_exp.tendsto (c - Real.log (2 * Real.pi) ) |>.comp hlog
  refine hexp.congr' ?_
  filter_upwards [hG_pos, hC_pos] with m hmG_pos hmC_pos
  rw [Real.exp_sub, Real.exp_log hmG_pos, Real.exp_log hmC_pos]

end

end Omega.Zeta
