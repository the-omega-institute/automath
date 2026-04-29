import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `prop:pom-oracle-critical-window-mdp`.

If the logarithmic oracle success splits eventually into a tail term and a soft-threshold
correction, then the normalized moderate-deviation exponent is the sum of their limits. -/
theorem paper_pom_oracle_critical_window_mdp (logSucc tailErr softErr : ℕ → ℝ)
    (s sigma gamma : ℝ) (hgamma : (1 : ℝ) / 2 < gamma ∧ gamma < 1)
    (hsigma : 0 < sigma)
    (htail :
      Filter.Tendsto (fun m : ℕ => tailErr m / ((m : ℝ) ^ (2 * gamma - 1)))
        Filter.atTop (nhds (-(s ^ 2 / (2 * sigma ^ 2)))))
    (hsoft :
      Filter.Tendsto (fun m : ℕ => softErr m / ((m : ℝ) ^ (2 * gamma - 1)))
        Filter.atTop (nhds 0))
    (hdecomp : ∀ᶠ m in Filter.atTop, logSucc m = tailErr m + softErr m) :
    Filter.Tendsto (fun m : ℕ => logSucc m / ((m : ℝ) ^ (2 * gamma - 1)))
      Filter.atTop (nhds (-(s ^ 2 / (2 * sigma ^ 2)))) := by
  have _hgamma_used : (1 : ℝ) / 2 < gamma ∧ gamma < 1 := hgamma
  have _hsigma_used : 0 < sigma := hsigma
  have hsum :
      Filter.Tendsto
        (fun m : ℕ =>
          tailErr m / ((m : ℝ) ^ (2 * gamma - 1)) +
            softErr m / ((m : ℝ) ^ (2 * gamma - 1)))
        Filter.atTop (nhds (-(s ^ 2 / (2 * sigma ^ 2)) + 0)) :=
    htail.add hsoft
  have hcongr :
      (fun m : ℕ => logSucc m / ((m : ℝ) ^ (2 * gamma - 1))) =ᶠ[Filter.atTop]
        fun m : ℕ =>
          tailErr m / ((m : ℝ) ^ (2 * gamma - 1)) +
            softErr m / ((m : ℝ) ^ (2 * gamma - 1)) := by
    filter_upwards [hdecomp] with m hm
    rw [hm]
    ring
  simpa using hsum.congr' hcongr.symm

end

end Omega.POM
