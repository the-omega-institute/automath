namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the branch-decomposition corollary.
    cor:branch-decomposition -/
theorem paper_gluing_failure_branch_decomposition
    (branchConstancy : Prop)
    (essentiallySurjective fullOnSummands disjointSummands canonicalEquivalence : Prop)
    (hEss : branchConstancy → essentiallySurjective)
    (hFull : branchConstancy → fullOnSummands)
    (hDisjoint : branchConstancy → disjointSummands)
    (hEquiv :
      essentiallySurjective ∧ fullOnSummands ∧ disjointSummands → canonicalEquivalence) :
    branchConstancy →
      essentiallySurjective ∧
        fullOnSummands ∧
        disjointSummands ∧ canonicalEquivalence := by
  intro hBranch
  have hEss' := hEss hBranch
  have hFull' := hFull hBranch
  have hDisjoint' := hDisjoint hBranch
  exact ⟨hEss', hFull', hDisjoint', hEquiv ⟨hEss', hFull', hDisjoint'⟩⟩

end Omega.Topos
