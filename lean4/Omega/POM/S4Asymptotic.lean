import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Omega.Folding.MomentSum

namespace Omega.POM

open Filter

/-- The fourth collision moment sequence `S₄(m)`. -/
noncomputable def s4Moment (m : ℕ) : ℝ :=
  momentSum 4 m

/-- The normalized fourth moment `S₄(m) / 16^m`. -/
noncomputable def normalizedFourthMoment (m : ℕ) : ℝ :=
  s4Moment m / (16 : ℝ) ^ m

/-- The paper normalization constant `h₄ = log (16 / r₄)`. -/
noncomputable def fourthCollisionEntropyRate (r4 : ℝ) : ℝ :=
  Real.log ((16 : ℝ) / r4)

/-- Paper-facing S₄ asymptotic wrapper: if the fourth moment has Perron growth
    `S₄(m) = Θ(r₄^m)`, then the normalized fourth moment is exactly `S₄(m)/16^m`,
    and the entropy-rate constant rewrites as `log 16 - log r₄`.
    cor:pom-s4-asymptotic -/
theorem paper_pom_s4_asymptotic
    (r4 : ℝ) (hr4 : 0 < r4)
    (hTheta : (fun m : ℕ => s4Moment m) =Θ[Filter.atTop] fun m => r4 ^ m) :
    ((fun m : ℕ => s4Moment m) =Θ[Filter.atTop] fun m => r4 ^ m) ∧
      (∀ m : ℕ, normalizedFourthMoment m = s4Moment m / (16 : ℝ) ^ m) ∧
      fourthCollisionEntropyRate r4 = Real.log ((16 : ℝ) / r4) ∧
      fourthCollisionEntropyRate r4 = Real.log (16 : ℝ) - Real.log r4 := by
  refine ⟨hTheta, ?_, rfl, ?_⟩
  · intro m
    rfl
  · unfold fourthCollisionEntropyRate
    rw [Real.log_div]
    · norm_num
    · exact ne_of_gt hr4

end Omega.POM
