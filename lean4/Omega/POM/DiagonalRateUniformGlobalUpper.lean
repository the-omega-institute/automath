import Omega.POM.DiagonalRateUniformGlobalMax

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-uniform-global-upper`. -/
theorem paper_pom_diagonal_rate_uniform_global_upper (n : ℕ) [NeZero n] (hn : 2 ≤ n) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 - 1 / (n : ℝ)) (w : Fin n → ℝ) (hw : IsProbabilityVector w) :
    pomDiagonalRate w δ ≤ pomDiagonalRate (fun _ : Fin n => (1 : ℝ) / n) δ := by
  have hn_nat_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_real_pos : (0 : ℝ) < n := by
    exact_mod_cast hn_nat_pos
  have hinv_nonneg : 0 ≤ (1 : ℝ) / n := by
    positivity
  have hδ1' : δ ≤ 1 := by
    have hupper : δ < 1 := by
      refine lt_of_lt_of_le hδ1 ?_
      linarith
    linarith
  simpa using
    (paper_pom_diagonal_rate_uniform_global_max (n := n) (δ := δ) hn hδ0 hδ1' (w := w) hw)

end Omega.POM
