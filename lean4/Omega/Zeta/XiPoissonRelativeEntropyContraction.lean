import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Poisson semigroup and entropy-dissipation package for
`prop:xi-poisson-relative-entropy-contraction`. -/
structure xi_poisson_relative_entropy_contraction_data where
  kl : ℝ → ℝ
  poissonStep : ℝ → ℝ → ℝ
  fisherKreinDissipation : ℝ → ℝ
  poissonSemigroupStep :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → poissonStep s t = t + s
  dataProcessingInequality :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → kl (poissonStep s t) ≤ kl t
  fisherKreinEqualityCriterion :
    ∀ t : ℝ, 0 ≤ t → kl t = kl 0 → fisherKreinDissipation t = 0

namespace xi_poisson_relative_entropy_contraction_data

/-- Equality in the entropy contraction is rigid precisely through vanishing
Fisher--Krein dissipation. -/
def equalityRigid (D : xi_poisson_relative_entropy_contraction_data) : Prop :=
  ∀ t : ℝ, 0 ≤ t → D.kl t = D.kl 0 → D.fisherKreinDissipation t = 0

end xi_poisson_relative_entropy_contraction_data

open xi_poisson_relative_entropy_contraction_data

/-- Paper label: `prop:xi-poisson-relative-entropy-contraction`. -/
theorem paper_xi_poisson_relative_entropy_contraction
    (D : xi_poisson_relative_entropy_contraction_data) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → D.kl (t + s) ≤ D.kl t) ∧
      (∀ t : ℝ, 0 ≤ t → D.kl t ≤ D.kl 0) ∧ D.equalityRigid := by
  refine ⟨?step, ?origin, ?rigid⟩
  · intro s t hs ht
    rw [← D.poissonSemigroupStep s t hs ht]
    exact D.dataProcessingInequality s t hs ht
  · intro t ht
    have hstep : D.kl (0 + t) ≤ D.kl 0 := by
      exact (show D.kl (0 + t) ≤ D.kl 0 from (by
        rw [← D.poissonSemigroupStep t 0 ht le_rfl]
        exact D.dataProcessingInequality t 0 ht le_rfl))
    simpa using hstep
  · intro t ht heq
    exact D.fisherKreinEqualityCriterion t ht heq

end Omega.Zeta
