import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.Zeta

private theorem xi_time_part60f_zg_zero_prefix_log_density_squeeze_to_one
    (x ε : ℕ → ℝ)
    (hlo : ∀ n, 1 - ε n ≤ x n)
    (hhi : ∀ n, x n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 1) := by
  have hlo' : Tendsto (fun n => 1 - ε n) atTop (𝓝 1) := by
    have : Tendsto (fun n => 1 - ε n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hε
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo' tendsto_const_nhds hlo hhi

/-- Paper label: `thm:xi-time-part60f-zg-zero-prefix-log-density`.
Assume the zero-prefix density factors as the Euler product for the first `n` primes times a tail
factor. If the tail defect is bounded by two vanishing envelopes (the square-prime and adjacent
prime-pair tails) and the normalized Euler product satisfies the Mertens asymptotic at `p_n`,
then the zero-prefix density has the same logarithmic asymptotic. -/
theorem paper_xi_time_part60f_zg_zero_prefix_log_density
    (prime dens eulerProduct tailFactor squareTail adjacentTail : ℕ → ℝ)
    (hdens : ∀ n, dens n = eulerProduct n * tailFactor n)
    (h_tail_lower : ∀ n, 1 - (squareTail n + adjacentTail n) ≤ tailFactor n)
    (h_tail_upper : ∀ n, tailFactor n ≤ 1)
    (h_square : Tendsto squareTail atTop (𝓝 0))
    (h_adjacent : Tendsto adjacentTail atTop (𝓝 0))
    (h_mertens :
      Tendsto
        (fun n =>
          eulerProduct n * Real.log (prime n) / Real.exp (-Real.eulerMascheroniConstant))
        atTop (𝓝 1)) :
    Tendsto
      (fun n => dens n * Real.log (prime n) / Real.exp (-Real.eulerMascheroniConstant))
      atTop (𝓝 1) := by
  have hdefect : Tendsto (fun n => squareTail n + adjacentTail n) atTop (𝓝 0) :=
    by simpa using h_square.add h_adjacent
  have htail :
      Tendsto tailFactor atTop (𝓝 1) := by
    exact
      xi_time_part60f_zg_zero_prefix_log_density_squeeze_to_one tailFactor
        (fun n => squareTail n + adjacentTail n) h_tail_lower h_tail_upper hdefect
  have hprod :
      Tendsto
        (fun n =>
          (eulerProduct n * Real.log (prime n) / Real.exp (-Real.eulerMascheroniConstant)) *
            tailFactor n)
        atTop (𝓝 (1 * 1)) := by
    exact h_mertens.mul htail
  simpa [hdens, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod

end Omega.Zeta
