import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbkPositiveNatomicExactnessCeiling

namespace Omega.Zeta

/-- Concrete wrapper for the pole-count optimality statement in the finite Padé-Jacobi shadow
model. Matching the first `2n` coefficients is equivalent to being the canonical shadow, no
distinct finite-depth shadow can match one more coefficient, and the odd-factorial lift reindexes
the coefficient range `k < 2n` to the odd exponents `2k + 1 ≤ 4n - 1`. -/
def xi_time_part9zbk_pole_count_optimality_statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ R : PadeJacobiShadow, finiteDepth R →
      (matchesToOrder m_phi R (2 * n) ↔ R = m_phi_n n)) ∧
    (¬ ∃ R : PadeJacobiShadow,
      finiteDepth R ∧ matchesToOrder m_phi R (2 * n + 1) ∧ R ≠ m_phi_n n) ∧
    (∀ k : ℕ, k < 2 * n ↔ 2 * k + 1 ≤ 4 * n - 1)

/-- Paper label: `thm:xi-time-part9zbk-pole-count-optimality`. The Padé-Jacobi identity gives the
uniqueness direction at order `2n`, the exactness ceiling forbids any distinct finite-depth shadow
from matching one more coefficient, and the odd-factorial lift is the arithmetic reindexing
`k ↦ 2k + 1`. -/
theorem paper_xi_time_part9zbk_pole_count_optimality :
    xi_time_part9zbk_pole_count_optimality_statement := by
  intro n hn
  refine ⟨?_, ?_, ?_⟩
  · intro R hFinite
    constructor
    · intro hMatch
      exact paper_xi_time_part9zbk_pade_jacobi_identity n hn R hFinite hMatch
    · intro hR
      subst hR
      intro k hk
      rfl
  · simpa [xi_time_part9zbk_positive_natomic_exactness_ceiling_statement] using
      paper_xi_time_part9zbk_positive_natomic_exactness_ceiling n hn
  · intro k
    omega

end Omega.Zeta
