import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-holographic-dimension-sum-bound`. -/
theorem paper_pom_holographic_dimension_sum_bound (f : ℝ → ℝ)
    (hlogφ : 0 < Real.log Real.goldenRatio)
    (hupper : ∀ γ, 0 ≤ γ → γ ≤ Real.log 2 → f γ + γ ≤ Real.log 2)
    (hattain : ∃ γ, 0 ≤ γ ∧ γ ≤ Real.log 2 ∧ f γ + γ = Real.log 2) :
    (∀ γ, 0 ≤ γ → γ ≤ Real.log 2 →
        f γ / Real.log Real.goldenRatio + γ / Real.log Real.goldenRatio ≤
          Real.log 2 / Real.log Real.goldenRatio) ∧
      ∃ γ, 0 ≤ γ ∧ γ ≤ Real.log 2 ∧
        f γ / Real.log Real.goldenRatio + γ / Real.log Real.goldenRatio =
          Real.log 2 / Real.log Real.goldenRatio := by
  refine ⟨?_, ?_⟩
  · intro γ hγ0 hγ2
    have hscaled :
        (f γ + γ) / Real.log Real.goldenRatio ≤
          Real.log 2 / Real.log Real.goldenRatio :=
      div_le_div_of_nonneg_right (hupper γ hγ0 hγ2) hlogφ.le
    simpa [add_div] using hscaled
  · rcases hattain with ⟨γ, hγ0, hγ2, hsum⟩
    refine ⟨γ, hγ0, hγ2, ?_⟩
    calc
      f γ / Real.log Real.goldenRatio + γ / Real.log Real.goldenRatio =
          (f γ + γ) / Real.log Real.goldenRatio := by rw [add_div]
      _ = Real.log 2 / Real.log Real.goldenRatio := by rw [hsum]

end Omega.POM
