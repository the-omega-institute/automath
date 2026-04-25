import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.POM

/-- The `q → ∞` Rényi endpoint attached to the growth rates `r q`. -/
def pom_maxfiber_exponent_equals_renyi_endpoint_endpoint (Λ : ℝ) (r : ℕ → ℝ) : Prop :=
  Tendsto (fun q : ℕ => Real.log (r q) / (q : ℝ)) atTop (𝓝 Λ)

/-- Paper label: `prop:pom-maxfiber-exponent-equals-renyi-endpoint`.
If the logarithmic Rényi growth rates satisfy the standard max-fiber squeeze
`q Λ ≤ log r_q ≤ q Λ + B`, then the normalized endpoint converges to `Λ`. -/
theorem paper_pom_maxfiber_exponent_equals_renyi_endpoint (Λ B : ℝ) (r : ℕ → ℝ)
    (hbound : ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) * Λ ≤ Real.log (r q) ∧ Real.log (r q) ≤ (q : ℝ) * Λ + B) :
    pom_maxfiber_exponent_equals_renyi_endpoint_endpoint Λ r := by
  have herror :
      ∀ q, 1 ≤ q →
        0 ≤ Real.log (r q) / (q : ℝ) - Λ ∧
          Real.log (r q) / (q : ℝ) - Λ ≤ B / (q : ℝ) := by
    intro q hq
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    rcases hbound q hq with ⟨hlow, hupp⟩
    have hqR_ne : (q : ℝ) ≠ 0 := ne_of_gt hqR
    have hlow' : Λ ≤ Real.log (r q) / (q : ℝ) := by
      field_simp [hqR_ne]
      linarith
    have hupp' : Real.log (r q) / (q : ℝ) ≤ Λ + B / (q : ℝ) := by
      field_simp [hqR_ne]
      linarith
    constructor
    · linarith
    · linarith
  have hupper_zero : Tendsto (fun q : ℕ => B / (q : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul B
  have herror_zero :
      Tendsto (fun q : ℕ => Real.log (r q) / (q : ℝ) - Λ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_zero ?_ ?_
    · exact (eventually_ge_atTop 1).mono fun q hq => (herror q hq).1
    · exact (eventually_ge_atTop 1).mono fun q hq => (herror q hq).2
  have hconst : Tendsto (fun _ : ℕ => Λ) atTop (𝓝 Λ) := tendsto_const_nhds
  have hsum :
      Tendsto (fun q : ℕ => Λ + (Real.log (r q) / (q : ℝ) - Λ)) atTop (𝓝 (Λ + 0)) := by
    exact hconst.add herror_zero
  have heq :
      (fun q : ℕ => Λ + (Real.log (r q) / (q : ℝ) - Λ)) =
        (fun q : ℕ => Real.log (r q) / (q : ℝ)) := by
    funext q
    ring
  simpa [pom_maxfiber_exponent_equals_renyi_endpoint_endpoint, heq] using hsum

end Omega.POM
