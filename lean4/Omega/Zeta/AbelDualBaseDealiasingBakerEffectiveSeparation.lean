namespace Omega.Zeta

/-- Paper label: `thm:abel-dual-base-dealiasing-baker-effective-separation`. The irrational-log
injectivity implication is recorded separately, while the Baker-type effective separation
hypothesis is composed with collision exclusion. -/
theorem paper_abel_dual_base_dealiasing_baker_effective_separation
    (irrationalLogs multiplicativelyIndependent phaseInjective effectiveSeparation
      collisionExcluded : Prop)
    (hInjective : irrationalLogs → phaseInjective)
    (hEffective : multiplicativelyIndependent → effectiveSeparation)
    (hCollision : effectiveSeparation → collisionExcluded) :
    (irrationalLogs → phaseInjective) ∧
      (multiplicativelyIndependent → effectiveSeparation ∧ collisionExcluded) := by
  refine ⟨hInjective, ?_⟩
  intro hIndependent
  exact ⟨hEffective hIndependent, hCollision (hEffective hIndependent)⟩

end Omega.Zeta
