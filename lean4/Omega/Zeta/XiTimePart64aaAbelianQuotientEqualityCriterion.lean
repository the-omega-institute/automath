import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part64aa-abelian-quotient-equality-criterion`. -/
theorem paper_xi_time_part64aa_abelian_quotient_equality_criterion
    (l2Equality fiberConstant offQuotientChannelsVanish : Prop)
    (h₁ : l2Equality ↔ fiberConstant)
    (h₂ : fiberConstant ↔ offQuotientChannelsVanish) :
    (l2Equality ↔ fiberConstant) ∧ (fiberConstant ↔ offQuotientChannelsVanish) ∧
      (l2Equality ↔ offQuotientChannelsVanish) := by
  exact ⟨h₁, h₂, h₁.trans h₂⟩

end Omega.Zeta
