import Omega.GroupUnification.GroupJGFoldSquarefreeExternalization

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-fiber-squarefree-prime-externalization`. -/
theorem paper_xi_fold_fiber_squarefree_prime_externalization :
    (∀ m : ℕ, Function.Injective (Omega.GroupUnification.foldPsi m)) ∧
      (∀ m : ℕ, Function.Bijective (Omega.GroupUnification.foldPsiToRange m)) := by
  exact
    ⟨Omega.GroupUnification.foldPsi_injective,
      Omega.GroupUnification.foldPsiToRange_bijective⟩

end Omega.Zeta
