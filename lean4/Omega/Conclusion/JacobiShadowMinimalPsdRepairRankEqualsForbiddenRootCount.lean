namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-jacobi-shadow-minimal-psd-repair-rank-equals-forbidden-root-count`. -/
theorem paper_conclusion_jacobi_shadow_minimal_psd_repair_rank_equals_forbidden_root_count
    (forbiddenCount repairRank negativeIndex : Nat)
    (hforb : forbiddenCount = negativeIndex)
    (hupper : repairRank ≤ negativeIndex)
    (hlower : negativeIndex ≤ repairRank) :
    repairRank = forbiddenCount := by
  exact (Nat.le_antisymm hupper hlower).trans hforb.symm

end Omega.Conclusion
