import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-half-exponent-needs-exp-moment-order`. Uniform consistency rules out
the subexponential blind-spot regime, so some positive exponential rate eventually lower-bounds
`log (Q m)`. -/
theorem paper_pom_half_exponent_needs_exp_moment_order (Q : ℕ → ℕ)
    (uniformlyConsistent : Prop)
    (hSubexpObstructs :
      (∀ c > 0, ∀ M : ℕ, ∃ m ≥ M, Real.log (Q m : ℝ) < c * (m : ℝ)) →
        ¬ uniformlyConsistent) :
    uniformlyConsistent →
      ∃ c > 0, ∃ M : ℕ, ∀ m ≥ M, c * (m : ℝ) ≤ Real.log (Q m : ℝ) := by
  intro hConsistent
  by_contra hNoGrowth
  have hSubexp :
      ∀ c > 0, ∀ M : ℕ, ∃ m ≥ M, Real.log (Q m : ℝ) < c * (m : ℝ) := by
    intro c hc M
    by_contra hNoWitness
    apply hNoGrowth
    refine ⟨c, hc, M, ?_⟩
    intro m hm
    by_cases hBound : c * (m : ℝ) ≤ Real.log (Q m : ℝ)
    · exact hBound
    · exfalso
      exact hNoWitness ⟨m, hm, lt_of_not_ge hBound⟩
  exact hSubexpObstructs hSubexp hConsistent

end Omega.POM
