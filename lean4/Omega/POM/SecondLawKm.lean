import Mathlib.Tactic
import Omega.POM.EntIncreaseEqualsKl

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Paper label: `cor:pom-second-law-Km`.

For the concrete fiber reflector `K_m = Q_m ∘ P_m`, implemented here as
`fiberUniformLift d (fiberMarginal d μ)`, the entropy increase is exactly the KL defect and is
therefore nonnegative. The zero case is the fixed-point condition for the reflector. -/
theorem paper_pom_second_law_km (d : X → ℕ) (hd : ∀ x, 0 < d x)
    (μ : FiberMicrostate d → ℝ)
    (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hμ_sum : Finset.univ.sum μ = 1)
    (hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d (fiberMarginal d μ)))
    (hkl_zero_iff :
      klDiv μ (fiberUniformLift d (fiberMarginal d μ)) = 0 ↔
        μ = fiberUniformLift d (fiberMarginal d μ)) :
    liftEntropy d (fiberUniformLift d (fiberMarginal d μ)) - liftEntropy d μ =
        klDiv μ (fiberUniformLift d (fiberMarginal d μ)) ∧
      0 ≤ liftEntropy d (fiberUniformLift d (fiberMarginal d μ)) - liftEntropy d μ ∧
      (liftEntropy d (fiberUniformLift d (fiberMarginal d μ)) - liftEntropy d μ = 0 ↔
        fiberUniformLift d (fiberMarginal d μ) = μ) := by
  have hπ_nonneg : ∀ x, 0 ≤ fiberMarginal d μ x := by
    intro x
    exact Finset.sum_nonneg fun i _ => hμ_nonneg ⟨x, i⟩
  have hledger :
      liftEntropy d (fiberUniformLift d (fiberMarginal d μ)) - liftEntropy d μ =
        klDiv μ (fiberUniformLift d (fiberMarginal d μ)) :=
    paper_pom_ent_increase_equals_kl d hd (fiberMarginal d μ) μ (by intro x; rfl)
      hμ_nonneg hπ_nonneg hμ_sum
  refine ⟨hledger, by simpa [hledger] using hkl_nonneg, ?_⟩
  constructor
  · intro hzero
    exact (hkl_zero_iff.mp (by simpa [hledger] using hzero)).symm
  · intro hfixed
    have hμ_eq : μ = fiberUniformLift d (fiberMarginal d μ) := hfixed.symm
    exact hledger.trans (hkl_zero_iff.mpr hμ_eq)

end

end Omega.POM
