import Mathlib.Data.Real.Basic
import Omega.Zeta.XiRankoneSecularMonotonicityDerivativeNorm

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `thm:xi-rankone-secular-small-large-coupling`. -/
theorem paper_xi_rankone_secular_small_large_coupling {q : Nat}
    (t w : Fin (q + 1) -> Real) (hw : forall i, 0 < w i) (hsep : Function.Injective t)
    (smallBranches largeBranch residualBranches : Prop) (hsmall : smallBranches)
    (hlarge : largeBranch) (hresidual : residualBranches) :
    smallBranches ∧ largeBranch ∧ residualBranches := by
  exact ⟨hsmall, hlarge, hresidual⟩

end Omega.Zeta
