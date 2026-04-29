import Omega.Folding.ModSemiringsSquarefreeNilpotentBranch

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-congruence-nilradical-reduced-quotient`. -/
theorem paper_xi_fold_congruence_nilradical_reduced_quotient (m : ℕ) :
    let n := Omega.foldModSemiringModulus m
    let r := Omega.foldModSemiringRadical m
    ((Finset.range n).filter (fun a => r ∣ a)).card = n / r ∧
      (Squarefree n ↔ ((Finset.range n).filter (fun a => a ≠ 0 ∧ r ∣ a)).card = 0) := by
  simpa using Omega.paper_fold_mod_semirings_squarefree_nilpotent_branch m

end Omega.Zeta
