import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Omega.Zeta.PhaseImplementationRankLimit

open Filter Topology

/-- Bounded nonneg / tends-to-infinity → quotient tends to zero.
    thm:xi-phase-implementation-rank-triple-characterization -/
theorem bounded_div_tendsto_infty_zero (f g : ℕ → ℝ)
    (hf : ∃ C, ∀ n, 0 ≤ f n ∧ f n ≤ C)
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  have hC_nn : 0 ≤ C := le_trans (hC 0).1 (hC 0).2
  have htend_abs : Tendsto (fun n => C / |g n|) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = C * 0 from (mul_zero C).symm]
    simp_rw [div_eq_mul_inv]
    have hg_abs : Tendsto (fun n => |g n|) atTop atTop :=
      tendsto_abs_atTop_atTop.comp hg
    exact tendsto_const_nhds.mul hg_abs.inv_tendsto_atTop
  apply squeeze_zero_norm _ htend_abs
  intro n
  rw [Real.norm_eq_abs, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  rw [abs_of_nonneg (hC n).1]
  exact (hC n).2

/-- Phase rank limit: `(r · g(n) + f(n)) / g(n) → r`.
    thm:xi-phase-implementation-rank-triple-characterization -/
theorem paper_xi_phase_implementation_rank_limit (r : ℝ)
    (f g : ℕ → ℝ)
    (hf : ∃ C, ∀ n, 0 ≤ f n ∧ f n ≤ C)
    (hg : Tendsto g atTop atTop)
    (hg_pos : ∀ᶠ n in atTop, 0 < g n) :
    Tendsto (fun n => (r * g n + f n) / g n) atTop (𝓝 r) := by
  have hfg := bounded_div_tendsto_infty_zero f g hf hg
  suffices h : Tendsto (fun n => r + f n / g n) atTop (𝓝 r) by
    apply h.congr'
    filter_upwards [hg_pos] with n hgn
    rw [add_div, mul_div_assoc, div_self (ne_of_gt hgn), mul_one]
  conv => rhs; rw [show r = r + 0 from (add_zero r).symm]
  exact tendsto_const_nhds.add hfg

/-- Paper-facing seeds wrapper for the phase implementation rank limit.
    thm:xi-phase-implementation-rank-triple-characterization -/
theorem paper_xi_phase_implementation_rank_limit_seeds (r : ℝ)
    (f g : ℕ → ℝ)
    (hf : ∃ C, ∀ n, 0 ≤ f n ∧ f n ≤ C)
    (hg : Tendsto g atTop atTop)
    (hg_pos : ∀ᶠ n in atTop, 0 < g n) :
    Tendsto (fun n => (r * g n + f n) / g n) atTop (𝓝 r) :=
  paper_xi_phase_implementation_rank_limit r f g hf hg hg_pos

/-- Package clone for the phase implementation rank limit.
    thm:xi-phase-implementation-rank-triple-characterization -/
theorem paper_xi_phase_implementation_rank_limit_package (r : ℝ)
    (f g : ℕ → ℝ)
    (hf : ∃ C, ∀ n, 0 ≤ f n ∧ f n ≤ C)
    (hg : Tendsto g atTop atTop)
    (hg_pos : ∀ᶠ n in atTop, 0 < g n) :
    Tendsto (fun n => (r * g n + f n) / g n) atTop (𝓝 r) :=
  paper_xi_phase_implementation_rank_limit_seeds r f g hf hg hg_pos

end Omega.Zeta.PhaseImplementationRankLimit
