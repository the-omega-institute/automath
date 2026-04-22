import Omega.OperatorAlgebra.BayesInverseZK

namespace Omega.OperatorAlgebra

/-- Paper label: `cor:op-algebra-zk-reflector-bayes`. The fixed points of the visible closure are
exactly the channels that factor through the Bayes inverse, and the simulator is uniquely
determined by restriction along the visible inclusion. -/
theorem paper_op_algebra_zk_reflector_bayes {M N T : Type*} (F : N → M) (Fsharp : M → N)
    (hsection : Function.LeftInverse Fsharp F) :
    ∀ Phi : M → T, fixedByVisibleClosure F Fsharp Phi → ∃! S : N → T, Phi = S ∘ Fsharp := by
  intro Phi hfixed
  obtain ⟨hfactor_iff, hsim_unique⟩ := paper_op_algebra_bayes_inverse_zk F Fsharp Phi hsection
  rcases hfactor_iff.mpr hfixed with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro S' hS'
  ext y
  calc
    S' y = Phi (F y) := hsim_unique hS' y
    _ = S y := (hsim_unique hS y).symm

end Omega.OperatorAlgebra
