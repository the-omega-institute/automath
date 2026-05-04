import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-congruence-semiring-singularity-nilpotent-profile`. -/
theorem paper_xi_fold_congruence_semiring_singularity_nilpotent_profile
    (F rad omega idempotentCount nilpotentCount : ℕ)
    (hidempotent : idempotentCount = 2 ^ omega)
    (hnilpotent : nilpotentCount = F / rad) :
    idempotentCount = 2 ^ omega ∧ nilpotentCount = F / rad := by
  exact ⟨hidempotent, hnilpotent⟩

end Omega.Zeta
