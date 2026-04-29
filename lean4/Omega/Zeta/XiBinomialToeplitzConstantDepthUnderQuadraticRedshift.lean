import Mathlib.Tactic
import Omega.Zeta.XiBinomialToeplitzScaleDepthExchange

namespace Omega.Zeta

noncomputable section

/-- The sparse scale chosen from the reciprocal moment-growth law. -/
def xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_m (c Λ_mom : ℝ) : ℕ :=
  Nat.ceil (c / Λ_mom)

/-- The uniform dominance depth bound obtained from the exchange estimate. -/
def xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_N_sharp
    (N0 C0 c : ℝ) : ℝ :=
  N0 + C0 / c

/-- Paper label: `cor:xi-binomial-toeplitz-constant-depth-under-quadratic-redshift`.
Choosing the sparse scale `m = ceil (c / Λ_mom)` forces `m * Λ_mom ≥ c`, so the scale-depth
exchange estimate becomes a uniform constant-depth bound `N_dom(m) ≤ N_sharp`. -/
theorem paper_xi_binomial_toeplitz_constant_depth_under_quadratic_redshift
    (N_dom : ℕ → ℝ) (N0 C0 c Λ_mom : ℝ) (hΛ : 0 < Λ_mom) (hc : 1 < c) (hC0 : 0 ≤ C0)
    (hscale :
      ∀ m : ℕ, 1 ≤ m → N_dom m ≤ N0 + C0 / ((m : ℝ) * Λ_mom)) :
    let m := xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_m c Λ_mom
    let N_sharp := xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_N_sharp N0 C0 c
    (N_dom m ≤ N0 + C0 / ((m : ℝ) * Λ_mom)) ∧
      c ≤ (m : ℝ) * Λ_mom ∧
      N_dom m ≤ N_sharp := by
  dsimp [xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_m,
    xi_binomial_toeplitz_constant_depth_under_quadratic_redshift_N_sharp]
  have hratio_pos : 0 < c / Λ_mom := by
    exact div_pos (lt_trans zero_lt_one hc) hΛ
  have hm_nat : 1 ≤ Nat.ceil (c / Λ_mom) := by
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hratio_pos)
  have hdom :
      N_dom (Nat.ceil (c / Λ_mom)) ≤
        N0 + C0 / (((Nat.ceil (c / Λ_mom) : ℕ) : ℝ) * Λ_mom) :=
    hscale (Nat.ceil (c / Λ_mom)) hm_nat
  have hceil : c / Λ_mom ≤ (Nat.ceil (c / Λ_mom) : ℝ) := Nat.le_ceil (c / Λ_mom)
  have hmul_ge : c ≤ (Nat.ceil (c / Λ_mom) : ℝ) * Λ_mom := by
    have hmul := mul_le_mul_of_nonneg_right hceil (le_of_lt hΛ)
    have hleft : (c / Λ_mom) * Λ_mom = c := by
      field_simp [hΛ.ne']
    simpa [hleft] using hmul
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hfrac :
      C0 / ((Nat.ceil (c / Λ_mom) : ℝ) * Λ_mom) ≤ C0 / c := by
    exact div_le_div_of_nonneg_left hC0 hc0 hmul_ge
  have hsharp :
      N_dom (Nat.ceil (c / Λ_mom)) ≤ N0 + C0 / c := by
    linarith
  simpa using
    paper_xi_binomial_toeplitz_scale_depth_exchange
      (N_dom (Nat.ceil (c / Λ_mom)) ≤
        N0 + C0 / (((Nat.ceil (c / Λ_mom) : ℕ) : ℝ) * Λ_mom))
      (c ≤ (Nat.ceil (c / Λ_mom) : ℝ) * Λ_mom)
      (N_dom (Nat.ceil (c / Λ_mom)) ≤ N0 + C0 / c)
      hdom hmul_ge hsharp

end

end Omega.Zeta
