import Omega.Folding.FixedFiberLipschitzOptimization

namespace Omega

/-- Paper label: `cor:fold-fixed-fiber-constant-lipschitz-optimization-np-complete`. The bounded
occurrence package just records NP-hardness, NP membership, and the inherited uniform Lipschitz
bound. -/
theorem paper_fold_fixed_fiber_constant_lipschitz_optimization_np_complete (Δ : ℕ)
    (npHard inNP : Prop) (hLipschitz : ∀ n, fixedFiberClauseDegree n ≤ Δ) :
    npHard → inNP → npHard ∧ inNP ∧ ∀ n, fixedFiberClauseDegree n ≤ Δ := by
  intro hNpHard hInNp
  exact ⟨hNpHard, hInNp, hLipschitz⟩

end Omega
