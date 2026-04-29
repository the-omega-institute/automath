import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Concrete sign-density and extremal data for the terminal `zm` cumulant oscillation.  The
prefix counts record the empirical positive/negative sign frequencies, while the last two fields
encode the full-support excursions and irrational-rotation nonperiodicity used by the paper. -/
structure xi_terminal_zm_cumulant_sign_density_extremes_data where
  xi_terminal_zm_cumulant_sign_density_extremes_cumulant : ℕ → ℝ
  xi_terminal_zm_cumulant_sign_density_extremes_positivePrefixCount : ℕ → ℕ
  xi_terminal_zm_cumulant_sign_density_extremes_negativePrefixCount : ℕ → ℕ
  xi_terminal_zm_cumulant_sign_density_extremes_positive_density_half_hyp :
    Tendsto
      (fun N : ℕ =>
        (xi_terminal_zm_cumulant_sign_density_extremes_positivePrefixCount N : ℝ) /
          (N + 1 : ℝ))
      atTop (nhds ((1 : ℝ) / 2))
  xi_terminal_zm_cumulant_sign_density_extremes_negative_density_half_hyp :
    Tendsto
      (fun N : ℕ =>
        (xi_terminal_zm_cumulant_sign_density_extremes_negativePrefixCount N : ℝ) /
          (N + 1 : ℝ))
      atTop (nhds ((1 : ℝ) / 2))
  xi_terminal_zm_cumulant_sign_density_extremes_extremes_full_hyp :
    ∀ R : ℝ, ∃ n : ℕ,
      R < |xi_terminal_zm_cumulant_sign_density_extremes_cumulant n|
  xi_terminal_zm_cumulant_sign_density_extremes_sign_flip_hyp :
    ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧
        xi_terminal_zm_cumulant_sign_density_extremes_cumulant n *
            xi_terminal_zm_cumulant_sign_density_extremes_cumulant (n + 1) <
          0
  xi_terminal_zm_cumulant_sign_density_extremes_nonperiodic_witness :
    ∀ period start : ℕ, 0 < period →
      ∃ n : ℕ,
        start ≤ n ∧
          xi_terminal_zm_cumulant_sign_density_extremes_cumulant (n + period) ≠
            xi_terminal_zm_cumulant_sign_density_extremes_cumulant n

namespace xi_terminal_zm_cumulant_sign_density_extremes_data

/-- Positive sign natural density `1/2`, expressed through the recorded prefix counts. -/
def xi_terminal_zm_cumulant_sign_density_extremes_positive_density_half
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) : Prop :=
  Tendsto
    (fun N : ℕ =>
      (D.xi_terminal_zm_cumulant_sign_density_extremes_positivePrefixCount N : ℝ) /
        (N + 1 : ℝ))
    atTop (nhds ((1 : ℝ) / 2))

/-- Negative sign natural density `1/2`, expressed through the recorded prefix counts. -/
def xi_terminal_zm_cumulant_sign_density_extremes_negative_density_half
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) : Prop :=
  Tendsto
    (fun N : ℕ =>
      (D.xi_terminal_zm_cumulant_sign_density_extremes_negativePrefixCount N : ℝ) /
        (N + 1 : ℝ))
    atTop (nhds ((1 : ℝ) / 2))

/-- Full extremal excursions of the terminal cumulant. -/
def xi_terminal_zm_cumulant_sign_density_extremes_extremes_full
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) : Prop :=
  ∀ R : ℝ, ∃ n : ℕ,
    R < |D.xi_terminal_zm_cumulant_sign_density_extremes_cumulant n|

/-- Arbitrarily late adjacent sign changes. -/
def xi_terminal_zm_cumulant_sign_density_extremes_infinitely_many_sign_flips
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧
      D.xi_terminal_zm_cumulant_sign_density_extremes_cumulant n *
          D.xi_terminal_zm_cumulant_sign_density_extremes_cumulant (n + 1) <
        0

/-- Eventual periodicity of the terminal cumulant sequence. -/
def xi_terminal_zm_cumulant_sign_density_extremes_eventually_periodic
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) : Prop :=
  ∃ period start : ℕ, 0 < period ∧
    ∀ n : ℕ, start ≤ n →
      D.xi_terminal_zm_cumulant_sign_density_extremes_cumulant (n + period) =
        D.xi_terminal_zm_cumulant_sign_density_extremes_cumulant n

end xi_terminal_zm_cumulant_sign_density_extremes_data

/-- Paper label: `cor:xi-terminal-zm-cumulant-sign-density-extremes`. -/
theorem paper_xi_terminal_zm_cumulant_sign_density_extremes
    (D : xi_terminal_zm_cumulant_sign_density_extremes_data) :
    D.xi_terminal_zm_cumulant_sign_density_extremes_positive_density_half ∧
      D.xi_terminal_zm_cumulant_sign_density_extremes_negative_density_half ∧
      D.xi_terminal_zm_cumulant_sign_density_extremes_extremes_full ∧
      D.xi_terminal_zm_cumulant_sign_density_extremes_infinitely_many_sign_flips ∧
      ¬ D.xi_terminal_zm_cumulant_sign_density_extremes_eventually_periodic := by
  refine
    ⟨D.xi_terminal_zm_cumulant_sign_density_extremes_positive_density_half_hyp,
      D.xi_terminal_zm_cumulant_sign_density_extremes_negative_density_half_hyp,
      D.xi_terminal_zm_cumulant_sign_density_extremes_extremes_full_hyp,
      D.xi_terminal_zm_cumulant_sign_density_extremes_sign_flip_hyp, ?_⟩
  intro hperiodic
  rcases hperiodic with ⟨period, start, hperiod_pos, hstable⟩
  rcases D.xi_terminal_zm_cumulant_sign_density_extremes_nonperiodic_witness period start
      hperiod_pos with
    ⟨n, hn_start, hn_ne⟩
  exact hn_ne (hstable n hn_start)

end Omega.Zeta
