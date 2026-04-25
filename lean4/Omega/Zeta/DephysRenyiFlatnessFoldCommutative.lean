import Omega.OperatorAlgebra.CommutativeRenyiExtremizersAlphaStable

namespace Omega.Zeta

/-- Paper label: `cor:dephys-renyi-flatness-fold-commutative`. This is the Zeta-facing wrapper of
the verified commutative finite-fold extremizer characterization. -/
theorem paper_dephys_renyi_flatness_fold_commutative {Ω X : Type*} [Fintype Ω]
    [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X] (fold : Ω -> X)
    (hfold : Function.Surjective fold) :
    Omega.OperatorAlgebra.op_algebra_commutative_renyi_extremizers_alpha_stable_statement fold := by
  exact Omega.OperatorAlgebra.paper_op_algebra_commutative_renyi_extremizers_alpha_stable
    fold hfold

end Omega.Zeta
