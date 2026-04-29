import Omega.OperatorAlgebra.FoldLiftGlobalSignFactorization

namespace Omega.OperatorAlgebra

/-- The paper-facing global sign on the fold normalizer. -/
noncomputable def globalSign {m : Nat} {d : Fin m → Nat} (τ : FoldFiberNormalizer d) : ℤˣ :=
  foldFiberNormalizerSign d τ

/-- Product of the visible odd-block sign characters. -/
noncomputable def visibleCharacterProduct {m : Nat} (d : Fin m → Nat) (τ : FoldFiberNormalizer d) :
    ℤˣ :=
  visibleOddBlockSign d τ

/-- Product of the hidden fiber sign characters. -/
noncomputable def fiberCharacterProduct {m : Nat} (d : Fin m → Nat) (τ : FoldFiberNormalizer d) :
    ℤˣ :=
  hiddenFiberProductSign d τ

/-- The global sign is the product of the visible odd-block character and the hidden fiber
character contribution.
    cor:op-algebra-fold-global-sign-unique-decomposition -/
theorem paper_op_algebra_fold_global_sign_unique_decomposition {m : Nat} (d : Fin m → Nat) :
    ∀ tau : FoldFiberNormalizer d,
      globalSign tau = visibleCharacterProduct d tau * fiberCharacterProduct d tau := by
  intro tau
  simpa [globalSign, visibleCharacterProduct, fiberCharacterProduct] using
    paper_op_algebra_fold_lift_global_sign_factorization d tau

end Omega.OperatorAlgebra
