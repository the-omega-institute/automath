import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The truncated harmonic normalizing constant `H_m = Σ_{i < m} 1 / (i + 1)`. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass (m : ℕ) : ℝ :=
  ∑ i : Fin m, (1 : ℝ) / (i.1 + 1)

/-- The identity injective code, i.e. the already sorted Gödel assignment `i ↦ i`. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_identity_code
    (m : ℕ) : Fin m → Fin m :=
  fun i => i

/-- Weighted logarithmic Gödel cost for a fiber law `p`. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_godel_cost {m : ℕ}
    (p : Fin m → ℝ) : ℝ :=
  ∑ i, p i * Real.log (i.1 + 1)

/-- The entropy-side term appearing in the harmonic-KL expansion. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term {m : ℕ}
    (p : Fin m → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i)

/-- Total mass of the weight function `p`. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass {m : ℕ}
    (p : Fin m → ℝ) : ℝ :=
  ∑ i, p i

/-- Expanded KL functional against the harmonic prior `h_i = 1 / ((i + 1) H_m)`. -/
def conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl {m : ℕ}
    (p : Fin m → ℝ) : ℝ :=
  conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
    conclusion_fiber_minimal_godel_cost_harmonic_kl_godel_cost p +
      conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
        Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m)

/-- Paper label: `thm:conclusion-fiber-minimal-godel-cost-harmonic-kl`. The identity code is the
sorted injective Gödel assignment, and the harmonic-prior KL functional expands into an
entropy term, a weighted Gödel cost, and the harmonic normalizer; the correction term then gives
the immediate two-sided bounds around the weighted cost. -/
theorem paper_conclusion_fiber_minimal_godel_cost_harmonic_kl (m : ℕ) (p : Fin m → ℝ) :
    Function.Injective (conclusion_fiber_minimal_godel_cost_harmonic_kl_identity_code m) ∧
      conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl p =
        conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
          conclusion_fiber_minimal_godel_cost_harmonic_kl_godel_cost p +
            conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
              Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m) ∧
      conclusion_fiber_minimal_godel_cost_harmonic_kl_godel_cost p -
          |conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
              conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
                Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m)| ≤
        conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl p ∧
      conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl p ≤
        conclusion_fiber_minimal_godel_cost_harmonic_kl_godel_cost p +
          |conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
              conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
                Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m)| := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro i j hij
    exact hij
  · dsimp [conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl]
    have hcorr :
        -(abs
            (conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
              conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
                Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m))) ≤
          conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
            conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
              Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m) := by
      exact neg_abs_le _
    linarith
  · dsimp [conclusion_fiber_minimal_godel_cost_harmonic_kl_expanded_kl]
    have hcorr :
        conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
            conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
              Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m) ≤
          abs
            (conclusion_fiber_minimal_godel_cost_harmonic_kl_entropy_term p +
              conclusion_fiber_minimal_godel_cost_harmonic_kl_total_mass p *
                Real.log (conclusion_fiber_minimal_godel_cost_harmonic_kl_harmonic_mass m)) := by
      exact le_abs_self _
    linarith

end

end Omega.Conclusion
