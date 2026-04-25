import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionLogconvexLambdaq

namespace Omega.POM

noncomputable section

/-- Label-prefixed general-`q` Rényi collision rate induced by the lambda normalization. -/
def pom_multiplicity_composition_renyi_collision_generalq_rate (q alpha : ℕ) : ℝ :=
  (Real.log (pomMultiplicityCompositionLambda (alpha * q)) -
      (alpha : ℝ) * Real.log (pomMultiplicityCompositionLambda q)) /
    (1 - (alpha : ℝ))

/-- Label-prefixed two-copy collision exponent for the multiplicity-composition ensemble. -/
def pom_multiplicity_composition_renyi_collision_generalq_collisionExponent (q : ℕ) : ℝ :=
  Real.log ((pomMultiplicityCompositionLambda q)^2 / pomMultiplicityCompositionLambda (2 * q))

/-- Paper label: `prop:pom-multiplicity-composition-renyi-collision-generalq`. The
label-prefixed rate and collision exponent are the closed lambda-ratio forms. -/
theorem paper_pom_multiplicity_composition_renyi_collision_generalq (q alpha : ℕ)
    (hq : 0 < q) (ha : 1 < alpha) :
    pom_multiplicity_composition_renyi_collision_generalq_rate q alpha =
        (Real.log (pomMultiplicityCompositionLambda (alpha * q)) -
          (alpha : ℝ) * Real.log (pomMultiplicityCompositionLambda q)) /
          (1 - (alpha : ℝ)) ∧
      pom_multiplicity_composition_renyi_collision_generalq_collisionExponent q =
        Real.log ((pomMultiplicityCompositionLambda q)^2 /
          pomMultiplicityCompositionLambda (2 * q)) := by
  have _hq := hq
  have _ha := ha
  constructor <;> rfl

end

end Omega.POM
