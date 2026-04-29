import Omega.POM.MultiplicityCompositionExactConditionalIid

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `prop:pom-multiplicity-composition-renewal-hit-prob`. -/
theorem paper_pom_multiplicity_composition_renewal_hit_prob
    (D : PomMultiplicityCompositionExactConditionalIidData) (lam : ℝ) (hlam : lam * D.rho = 1) :
    (D.paths.sum fun path => D.pathProb path) =
        D.rho ^ D.L * pomPartitionFunction D.q D.paths ∧
      pomPartitionFunction D.q D.paths =
        lam ^ D.L * (D.paths.sum fun path => D.pathProb path) := by
  have hhit :=
    (paper_pom_multiplicity_composition_exact_conditional_iid D).2.1
  refine ⟨hhit, ?_⟩
  have hscale :
      lam ^ D.L * (D.paths.sum fun path => D.pathProb path) =
        pomPartitionFunction D.q D.paths := by
    rw [hhit, ← mul_assoc, ← mul_pow, hlam, one_pow, one_mul]
  exact hscale.symm

end Omega.POM
