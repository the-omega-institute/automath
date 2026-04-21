import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointPoissonWeightScaling

namespace Omega.Zeta

private lemma succ_le_pow_of_two_le (m n : ℕ) (hm : 2 ≤ m) : n + 1 ≤ m ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 2 ≤ 2 * (n + 1) := by omega
        _ ≤ m * m ^ n := Nat.mul_le_mul hm ih
        _ = m ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Paper label: `cor:xi-nohair-fixedpoint-flux-closure`.
If every iterated `ψ_m` pushforward has uniformly bounded endpoint flux norm, the initial flux
must vanish. Otherwise the linear scaling law forces geometric growth. -/
theorem paper_xi_nohair_fixedpoint_flux_closure (m : ℕ) (hm : 1 < m) (zeros : Finset ℂ) (M : ℝ)
    (hbounded : ∀ n : ℕ, ‖endpointFlux (pushZerosByPsi (m ^ n) zeros)‖ ≤ M) :
    endpointFlux zeros = 0 := by
  have hm2 : 2 ≤ m := by omega
  by_contra hflux
  have hM_nonneg : 0 ≤ M := by
    exact le_trans (norm_nonneg _) (hbounded 0)
  have hflux_pos : 0 < ‖endpointFlux zeros‖ := by
    exact norm_pos_iff.mpr hflux
  obtain ⟨n, hn⟩ := exists_nat_gt (M / ‖endpointFlux zeros‖)
  let N : ℕ := n + 1
  have hratio_lt : M / ‖endpointFlux zeros‖ < N := by
    have hn_lt : (n : ℝ) < N := by
      exact_mod_cast Nat.lt_succ_self n
    linarith
  have hpow_ge : (N : ℝ) ≤ m ^ N := by
    exact_mod_cast le_trans (Nat.le_succ N) (succ_le_pow_of_two_le m N hm2)
  have hN_pos : 1 ≤ N := by
    simp [N]
  have hm_pow : 1 < m ^ N := by
    have hm_pos : 0 < m := by omega
    have hpow_ge_m : m ≤ m ^ N := by
      simpa [pow_one] using Nat.pow_le_pow_right hm_pos hN_pos
    exact lt_of_lt_of_le hm hpow_ge_m
  have hnorm :
      ‖endpointFlux (pushZerosByPsi (m ^ N) zeros)‖ = (m ^ N : ℝ) * ‖endpointFlux zeros‖ := by
    rw [paper_xi_endpoint_poisson_weight_scaling (m ^ N) hm_pow zeros, norm_mul]
    simp
  have hlower : M < (m ^ N : ℝ) * ‖endpointFlux zeros‖ := by
    have hNmul : M < (N : ℝ) * ‖endpointFlux zeros‖ := by
      exact (div_lt_iff₀ hflux_pos).mp hratio_lt
    have hmono :
        (N : ℝ) * ‖endpointFlux zeros‖ ≤ (m ^ N : ℝ) * ‖endpointFlux zeros‖ := by
      exact mul_le_mul_of_nonneg_right hpow_ge (le_of_lt hflux_pos)
    exact lt_of_lt_of_le hNmul hmono
  have hupper : (m ^ N : ℝ) * ‖endpointFlux zeros‖ ≤ M := by
    simpa [hnorm] using hbounded N
  exact (not_lt_of_ge hupper) hlower

end Omega.Zeta
