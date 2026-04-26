import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-maxfiber-relative-entropy-loss`. -/
theorem paper_conclusion_maxfiber_relative_entropy_loss {Ω X : Type*} [Fintype Ω]
    [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X] (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    Omega.OperatorAlgebra.foldIndexEqualsMaxFiber fold ∧
      Omega.OperatorAlgebra.foldPointMassLossFormula fold ∧
      Omega.OperatorAlgebra.foldMaxLossCharacterization fold := by
  exact Omega.OperatorAlgebra.paper_op_algebra_index_extremal_entropy_loss_maxfiber fold hfold

end Omega.Conclusion
