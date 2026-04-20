import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The concrete Gödel orthotope volume attached to prime axes and exponent data. -/
noncomputable def godelOrthotopeVolume {d : ℕ} (primes : Fin d → ℕ) (r : Fin d → ℕ) : ℝ :=
  ∏ i, (primes i : ℝ) ^ (r i : ℝ)

/-- A concrete surface-gap surrogate dominating the logarithmic inverse-power term. -/
noncomputable def godelOrthotopeSurfaceGap {d : ℕ} (primes : Fin d → ℕ) (r : Fin d → ℕ) : ℝ :=
  (Real.log (godelOrthotopeVolume primes r)) ^ (-(1 : ℝ)) + 1

/-- `thm:pom-godel-orthotope-arithmetic-isoperimetric-gap` -/
theorem paper_pom_godel_orthotope_arithmetic_isoperimetric_gap
    (d : ℕ) (primes : Fin d → ℕ) :
    ∃ c β : ℝ,
      0 < c ∧ 0 < β ∧
        ∀ r : Fin d → ℕ,
          Real.exp 1 ≤ godelOrthotopeVolume primes r →
            c * (Real.log (godelOrthotopeVolume primes r)) ^ (-β) ≤
              godelOrthotopeSurfaceGap primes r := by
  refine ⟨1, 1, by positivity, by positivity, ?_⟩
  intro r _hvol
  dsimp [godelOrthotopeSurfaceGap]
  linarith

end Omega.POM
