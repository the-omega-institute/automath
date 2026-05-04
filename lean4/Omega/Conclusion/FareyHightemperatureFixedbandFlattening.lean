import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.Conclusion

/-- The operator norm on a finite diagonal Fourier band, expressed as the finite sum norm of
eigenvalue defects.  This concrete norm dominates each coordinate and has the same zero limit as
the finite maximum. -/
noncomputable def conclusion_farey_hightemperature_fixedband_flattening_band_norm
    {band : ℕ} (eigenvalueDefect : Fin band → ℕ → ℝ) (tau : ℕ) : ℝ :=
  ∑ n : Fin band, |eigenvalueDefect n tau|

/-- Paper label: `thm:conclusion-farey-hightemperature-fixedband-flattening`.
If each fixed Fourier coordinate has vanishing high-temperature eigenvalue defect, then every
fixed finite Fourier band flattens in operator norm. -/
theorem paper_conclusion_farey_hightemperature_fixedband_flattening
    {band : ℕ} (eigenvalueDefect : Fin band → ℕ → ℝ)
    (hpoint :
      ∀ n : Fin band, Tendsto (fun tau : ℕ => eigenvalueDefect n tau) atTop (𝓝 0)) :
    Tendsto
      (fun tau : ℕ =>
        conclusion_farey_hightemperature_fixedband_flattening_band_norm eigenvalueDefect tau)
      atTop (𝓝 0) := by
  unfold conclusion_farey_hightemperature_fixedband_flattening_band_norm
  have hsum :
      Tendsto (fun tau : ℕ => ∑ n : Fin band, |eigenvalueDefect n tau|)
        atTop (𝓝 (∑ _n : Fin band, (0 : ℝ))) := by
    apply tendsto_finset_sum
    intro n _hn
    simpa using (hpoint n).abs
  simpa using hsum

end Omega.Conclusion
