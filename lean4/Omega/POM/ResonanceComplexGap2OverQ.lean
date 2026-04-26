import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- Paper label: `cor:pom-resonance-complex-gap-2overq`. -/
theorem paper_pom_resonance_complex_gap_2overq (φ : ℝ) (r η g : ℕ → ℝ) (hφ : 1 < φ)
    (hR : Filter.Tendsto (fun q : ℕ => Real.log (r q / r (q - 2))) Filter.atTop
      (nhds (Real.log φ)))
    (hr : Filter.Tendsto (fun q : ℕ => Real.log (r q) / (q : ℝ)) Filter.atTop
      (nhds (Real.log φ / 2)))
    (heta : Filter.Tendsto (fun q : ℕ => Real.log (η q)) Filter.atTop (nhds 0))
    (hrel : ∀ᶠ q in Filter.atTop,
      Real.log (η q) = Real.log (r q / r (q - 2)) - g q * Real.log (r q)) :
    Filter.Tendsto (fun q : ℕ => (q : ℝ) * g q) Filter.atTop (nhds 2) := by
  have hlogφ_pos : 0 < Real.log φ := Real.log_pos hφ
  have hlogφ_ne : Real.log φ ≠ 0 := ne_of_gt hlogφ_pos
  have hhalf_pos : 0 < Real.log φ / 2 := by positivity
  have hden_pos :
      ∀ᶠ q : ℕ in atTop, 0 < Real.log (r q) / (q : ℝ) := by
    exact hr.eventually (isOpen_Ioi.mem_nhds hhalf_pos)
  have hnum :
      Tendsto
        (fun q : ℕ => Real.log (r q / r (q - 2)) - Real.log (η q))
        atTop (nhds (Real.log φ - 0)) :=
    hR.sub heta
  have hquot :
      Tendsto
        (fun q : ℕ =>
          (Real.log (r q / r (q - 2)) - Real.log (η q)) /
            (Real.log (r q) / (q : ℝ)))
        atTop (nhds ((Real.log φ - 0) / (Real.log φ / 2))) := by
    exact hnum.div hr (by positivity)
  have hquot_two :
      Tendsto
        (fun q : ℕ =>
          (Real.log (r q / r (q - 2)) - Real.log (η q)) /
            (Real.log (r q) / (q : ℝ)))
        atTop (nhds 2) := by
    have hlim : (Real.log φ - 0) / (Real.log φ / 2) = 2 := by
      calc
        (Real.log φ - 0) / (Real.log φ / 2) = Real.log φ / (Real.log φ / 2) := by ring
        _ = 2 := by field_simp [hlogφ_ne]
    have hlim' : Real.log φ / (Real.log φ / 2) = 2 := by
      field_simp [hlogφ_ne]
    simpa [hlim, hlim'] using hquot
  refine hquot_two.congr' ?_
  filter_upwards [hrel, hden_pos] with q hrelq hdenq
  have hq_ne : (q : ℝ) ≠ 0 := by
    intro hq
    rw [hq, div_zero] at hdenq
    linarith
  have hlogr_ne : Real.log (r q) ≠ 0 := by
    intro hlogr
    rw [hlogr, zero_div] at hdenq
    linarith
  rw [hrelq]
  field_simp [hq_ne, hlogr_ne]
  ring

end Omega.POM
