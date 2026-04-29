import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-poisson-cauchy-fisher-krein-tail-half-var2`. -/
theorem paper_xi_poisson_cauchy_fisher_krein_tail_half_var2 (I err : ℕ → ℝ) (Var : ℝ)
    (hI : ∀ t : ℕ, I t = (1 / 2) * Var ^ 2 / ((t : ℝ) + 1) ^ 5 + err t)
    (herr :
      Filter.Tendsto (fun t : ℕ => ((t : ℝ) + 1) ^ 5 * err t) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℕ => ((t : ℝ) + 1) ^ 5 * I t) Filter.atTop
      (nhds ((1 / 2) * Var ^ 2)) := by
  let c : ℝ := (1 / 2) * Var ^ 2
  have hcongr :
      (fun t : ℕ => ((t : ℝ) + 1) ^ 5 * I t) =
        fun t : ℕ => c + ((t : ℝ) + 1) ^ 5 * err t := by
    funext t
    rw [hI t]
    have hpow_ne : ((t : ℝ) + 1) ^ 5 ≠ 0 := by positivity
    field_simp [c, hpow_ne]
    ring
  rw [hcongr]
  simpa [c] using (tendsto_const_nhds.add herr)

end

end Omega.Zeta
