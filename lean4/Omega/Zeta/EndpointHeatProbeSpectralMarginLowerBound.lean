import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Rewriting the Rayleigh lower bound with the central-binomial identity gives the advertised
endpoint-probe margin bound.
`thm:xi-endpoint-heat-probe-spectral-margin-lower-bound` -/
theorem paper_xi_endpoint_heat_probe_spectral_margin_lower_bound (N : ℕ) (aN «λmin» : ℝ)
    (hN : 1 ≤ N)
    (hRayleigh :
      «λmin» * (Finset.sum (Finset.range (N + 1)) (fun k => (Nat.choose N k : ℝ)^2)) ≤
        (4 : ℝ)^N * aN) :
    «λmin» * (Nat.choose (2 * N) N : ℝ) ≤ (4 : ℝ)^N * aN := by
  let _ := hN
  have hsum : Finset.sum (Finset.range (N + 1)) (fun k => (Nat.choose N k : ℝ)^2) =
      (Nat.choose (2 * N) N : ℝ) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun k => (Nat.choose N k : ℝ)^2) =
          ((Finset.sum (Finset.range (N + 1)) (fun k => (Nat.choose N k)^2) : ℕ) : ℝ) := by
            simp
      _ = (Nat.choose (2 * N) N : ℝ) := by
            norm_num [Nat.sum_range_choose_sq]
  simpa [hsum] using hRayleigh

end Omega.Zeta
