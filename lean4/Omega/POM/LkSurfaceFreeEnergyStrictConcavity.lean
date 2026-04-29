import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-Lk-surface-free-energy-strict-concavity`. -/
theorem paper_pom_lk_surface_free_energy_strict_concavity (q gpp : ℝ → ℝ)
    (hq : ∀ t > 0, 0 < q t ∧ q t < 1)
    (hgpp : ∀ t > 0,
      gpp t =
        - q t / ((1 + q t)^2 * t * (4 + t)) -
          q t * (t + 2) / ((1 + q t) * (t * (4 + t)) * Real.sqrt (t * (4 + t)))) :
    ∀ t > 0, gpp t < 0 := by
  intro t ht
  rw [hgpp t ht]
  obtain ⟨hqt_pos, hqt_lt_one⟩ := hq t ht
  have h1qt_pos : 0 < 1 + q t := by linarith
  have h4t_pos : 0 < 4 + t := by linarith
  have htt4_pos : 0 < t * (4 + t) := mul_pos ht h4t_pos
  have hsqrt_pos : 0 < Real.sqrt (t * (4 + t)) := Real.sqrt_pos.mpr htt4_pos
  have hden1_pos : 0 < (1 + q t)^2 * t * (4 + t) := by positivity
  have hden2_pos : 0 < (1 + q t) * (t * (4 + t)) * Real.sqrt (t * (4 + t)) := by positivity
  have hterm1 : -q t / ((1 + q t)^2 * t * (4 + t)) < 0 := by
    have hfrac_pos : 0 < q t / ((1 + q t)^2 * t * (4 + t)) := by
      exact div_pos hqt_pos hden1_pos
    have hneg : -(q t / ((1 + q t)^2 * t * (4 + t))) < 0 := by linarith
    simpa [neg_div] using hneg
  have ht2_pos : 0 < t + 2 := by linarith
  have hterm2_pos :
      0 < q t * (t + 2) / ((1 + q t) * (t * (4 + t)) * Real.sqrt (t * (4 + t))) := by
    have hnum2_pos : 0 < q t * (t + 2) := mul_pos hqt_pos ht2_pos
    exact div_pos hnum2_pos hden2_pos
  linarith

end Omega.POM
