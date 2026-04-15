import Omega.Topos.BranchDecomposition

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for global branch decomposition under branch constancy in
    `2026_conservative_extension_chain_state_forcing_apal`.
    cor:branch-decomposition -/
theorem paper_conservative_extension_branch_decomposition
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
        disjointSummands ∧ canonicalEquivalence :=
  paper_gluing_failure_branch_decomposition
    branchConstancy essentiallySurjective fullOnSummands disjointSummands canonicalEquivalence
    hEss hFull hDisjoint hEquiv

end Omega.Topos
